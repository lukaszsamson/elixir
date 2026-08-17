# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

Code.require_file("../../test_helper.exs", __DIR__)

defmodule Mix.Sync.LockTest do
  use ExUnit.Case, async: true

  alias Mix.Sync.Lock

  @lock_key Atom.to_string(__MODULE__)

  test "executes functions" do
    assert Lock.with_lock(@lock_key, fn -> :it_works! end) == :it_works!
    assert Lock.with_lock(@lock_key, fn -> :still_works! end) == :still_works!
  end

  test "releases lock on error" do
    assert_raise RuntimeError, fn ->
      Lock.with_lock(@lock_key, fn -> raise "oops" end)
    end

    assert Lock.with_lock(@lock_key, fn -> :still_works! end) == :still_works!
  end

  test "releases lock on exit" do
    {_pid, ref} =
      spawn_monitor(fn ->
        Lock.with_lock(@lock_key, fn -> Process.exit(self(), :kill) end)
      end)

    assert_receive {:DOWN, ^ref, _, _, _}
    assert Lock.with_lock(@lock_key, fn -> :still_works! end) == :still_works!
  end

  test "blocks until released" do
    parent = self()

    task =
      Task.async(fn ->
        Lock.with_lock(@lock_key, fn ->
          send(parent, :locked)
          assert_receive :will_lock
          :it_works!
        end)
      end)

    assert_receive :locked
    send(task.pid, :will_lock)
    assert Lock.with_lock(@lock_key, fn -> :still_works! end) == :still_works!
    assert Task.await(task) == :it_works!
  end

  @tag :capture_log
  test "blocks until released on error" do
    parent = self()

    {pid, ref} =
      spawn_monitor(fn ->
        Lock.with_lock(@lock_key, fn ->
          send(parent, :locked)
          assert_receive :will_lock
          raise "oops"
        end)
      end)

    assert_receive :locked
    send(pid, :will_lock)
    assert Lock.with_lock(@lock_key, fn -> :still_works! end) == :still_works!
    assert_receive {:DOWN, ^ref, _, _, _}
  end

  test "blocks until released on exit" do
    parent = self()

    {pid, ref} =
      spawn_monitor(fn ->
        Lock.with_lock(@lock_key, fn ->
          send(parent, :locked)
          assert_receive :will_not_lock
        end)
      end)

    assert_receive :locked
    Process.exit(pid, :kill)
    assert Lock.with_lock(@lock_key, fn -> :still_works! end) == :still_works!
    assert_receive {:DOWN, ^ref, _, _, _}
  end

  test "schedules and releases on exit" do
    assert Lock.with_lock(@lock_key, fn ->
             {pid, ref} =
               spawn_monitor(fn ->
                 Lock.with_lock(@lock_key, fn ->
                   raise "this will never be invoked"
                 end)
               end)

             Process.exit(pid, :kill)
             assert_receive {:DOWN, ^ref, _, _, :killed}
             :it_works!
           end) == :it_works!

    assert Lock.with_lock(@lock_key, fn -> :still_works! end) == :still_works!
  end

  @tag :tmp_dir
  test "property test with file access", %{tmp_dir: tmp_dir} do
    # Spawn N concurrent processes incrementing number in a file
    n = 10
    number_path = Path.join(tmp_dir, "number.txt")

    File.write!(number_path, "0")

    refs =
      for _ <- 1..n do
        spawn_monitor(fn ->
          Lock.with_lock(@lock_key, fn ->
            number = number_path |> File.read!() |> String.to_integer()
            new_number = number + 1
            File.write!(number_path, Integer.to_string(new_number))

            assert File.read!(number_path) == Integer.to_string(new_number)

            # Terminate without unlocking in random cases
            case Enum.random(1..2) do
              1 -> Process.exit(self(), :kill)
              2 -> :ok
            end
          end)
        end)
        |> elem(1)
      end

    await_monitors(refs)

    assert File.read!(number_path) == Integer.to_string(n)
  end

  test "lock can be acquired multiple times by the same process" do
    {_pid, ref} =
      spawn_monitor(fn ->
        Lock.with_lock(@lock_key, fn ->
          Lock.with_lock(@lock_key, fn ->
            Process.exit(self(), :kill)
          end)
        end)
      end)

    assert_receive {:DOWN, ^ref, _, _, _}

    assert Lock.with_lock(@lock_key, fn ->
             Lock.with_lock(@lock_key, fn ->
               :still_works!
             end)
           end) == :still_works!
  end

  test "calls :on_taken when the lock is held by a different process" do
    parent = self()

    {pid, ref} =
      spawn_monitor(fn ->
        Lock.with_lock(@lock_key, fn ->
          send(parent, :locked)
          assert_receive :will_lock
        end)
      end)

    assert_receive :locked

    on_taken = fn os_pid ->
      send(pid, :will_lock)
      send(self(), {:on_taken_called, os_pid})
    end

    assert Lock.with_lock(@lock_key, fn -> :it_works! end, on_taken: on_taken) == :it_works!

    os_pid = System.pid()
    assert_receive {:on_taken_called, ^os_pid}

    assert_receive {:DOWN, ^ref, _, _, _}
  end

  # A truncated or empty lock file must be recovered (treated as stale and
  # repaired) without ever letting two processes hold the lock at once. These
  # states can be left behind by a writer that was interrupted mid-write, or by
  # an older version. Each seed exercises a different malformed shape.
  @malformed_seeds [
    empty: "",
    switch_only_zero: <<0>>,
    switch_only_one: <<1>>,
    wrong_size_valid_switch: <<0, 1, 2, 3>>,
    garbage: :binary.copy(<<7>>, 40)
  ]

  for {label, seed} <- @malformed_seeds do
    test "recovers from a #{label} lock file without letting two holders overlap" do
      seed = unquote(seed)
      key = unique_key()
      dir = lock_dir(key)
      File.mkdir_p!(dir)
      File.write!(Path.join(dir, "lock_0"), seed)

      parent = self()
      token = make_ref()

      {holder, holder_ref} =
        spawn_monitor(fn ->
          Lock.with_lock(key, fn ->
            send(parent, {:holding, token})

            receive do
              {:release, ^token} -> :ok
            after
              5000 -> :ok
            end
          end)
        end)

      # The recovering process must be able to acquire the malformed lock.
      assert_receive {:holding, ^token}, 5000

      # After recovery, lock_0 must be a well-formed switch file: a 1-byte
      # switch plus two equal segments, i.e. an odd size greater than one.
      size = File.stat!(Path.join(dir, "lock_0")).size
      assert size > 1 and rem(size, 2) == 1

      # A second contender must NOT be able to enter while the first holds.
      {_b, b_ref} =
        spawn_monitor(fn ->
          Lock.with_lock(key, fn -> send(parent, {:entered, token}) end)
        end)

      refute_receive {:entered, ^token}, 800

      # Once released, the second contender proceeds normally.
      send(holder, {:release, token})
      assert_receive {:entered, ^token}, 5000
      assert_receive {:DOWN, ^holder_ref, _, _, _}
      assert_receive {:DOWN, ^b_ref, _, _, _}
    end
  end

  @tag :tmp_dir
  test "many contenders on a malformed lock file never overlap or lose updates", %{
    tmp_dir: tmp_dir
  } do
    for seed <- ["", <<1>>] do
      key = unique_key()
      dir = lock_dir(key)
      File.mkdir_p!(dir)
      File.write!(Path.join(dir, "lock_0"), seed)

      number_path = Path.join(tmp_dir, "n_#{System.unique_integer([:positive])}")
      File.write!(number_path, "0")

      # index 1: processes currently inside the critical section
      # index 2: max ever observed concurrently (must stay 1)
      gauge = :atomics.new(2, [])
      n = 15

      refs =
        for _ <- 1..n do
          spawn_monitor(fn ->
            Lock.with_lock(key, fn ->
              current = :atomics.add_get(gauge, 1, 1)
              bump_max(gauge, current)
              number = number_path |> File.read!() |> String.to_integer()
              File.write!(number_path, Integer.to_string(number + 1))
              Process.sleep(2)
              :atomics.sub(gauge, 1, 1)
            end)
          end)
          |> elem(1)
        end

      await_monitors(refs)

      assert :atomics.get(gauge, 2) == 1, "critical section was entered concurrently"
      assert File.read!(number_path) == Integer.to_string(n)
    end
  end

  # This is the root scenario behind the recycled-port deadlock: a stale
  # port_P is still hard-linked at lock_0 when the OS hands port P to a new
  # process. Creating the new port_P must detach the pathname onto a fresh
  # inode, leaving lock_0 (the original inode) untouched.
  @tag :tmp_dir
  test "switch_file_create! detaches an existing hard-linked name onto a new inode",
       %{tmp_dir: tmp_dir} do
    port_path = Path.join(tmp_dir, "port_1234")
    lock_path = Path.join(tmp_dir, "lock_0")

    old_info = Lock.encode_lock_info(1234, "111")
    Lock.switch_file_create!(port_path, old_info)
    :ok = File.ln(port_path, lock_path)

    new_info = Lock.encode_lock_info(1234, "222")
    Lock.switch_file_create!(port_path, new_info)

    # lock_0 keeps the original inode and content, port_P is a new inode
    assert Lock.switch_file_read(lock_path) == {:ok, old_info}
    assert Lock.switch_file_read(port_path) == {:ok, new_info}

    if match?({:unix, _}, :os.type()) do
      assert File.stat!(lock_path).inode != File.stat!(port_path).inode
      assert File.stat!(lock_path).links == 1
    end
  end

  @tag :tmp_dir
  test "switch_file_create! raises and does not write when removal fails", %{tmp_dir: tmp_dir} do
    # A directory cannot be unlinked with File.rm/1, which reliably forces
    # the removal-failure branch. Writing must not be attempted afterwards.
    port_path = Path.join(tmp_dir, "port_1234")
    File.mkdir_p!(Path.join(port_path, "child"))

    assert_raise File.Error, fn ->
      Lock.switch_file_create!(port_path, Lock.encode_lock_info(1234, "111"))
    end

    assert File.dir?(port_path)
    assert File.exists?(Path.join(port_path, "child"))
  end

  test "decode_lock_info rejects content that is not exactly the fixed encoded size" do
    info = Lock.encode_lock_info(1234, "567")
    assert byte_size(info) == 37
    assert Lock.decode_lock_info(info) == {1234, "567"}

    # Well-shaped but wrong-sized content must not decode to a port
    assert Lock.decode_lock_info(<<1234::unsigned-integer-32, 0>>) == :error
    assert Lock.decode_lock_info(<<1234::unsigned-integer-32, 2, "ab", "1234567">>) == :error
    assert Lock.decode_lock_info(info <> <<0>>) == :error
    assert Lock.decode_lock_info("") == :error
  end

  @tag :tmp_dir
  test "fetch_probe_port treats a lock file naming our own port as stale", %{tmp_dir: tmp_dir} do
    # A stale lock_1+ can name a port later recycled to us. Probing must not
    # connect to our own listening socket, which would deadlock.
    lock_path = Path.join(tmp_dir, "lock_1")
    Lock.switch_file_create!(lock_path, Lock.encode_lock_info(4321, "111"))

    assert Lock.fetch_probe_port(lock_path, 4321) == {:error, :own_port}
    assert Lock.fetch_probe_port(lock_path, 5555) == {:ok, 4321, "111"}
  end

  test "normal use leaves lock_0 as a well-formed switch file" do
    key = unique_key()
    assert Lock.with_lock(key, fn -> :ok end) == :ok

    size = File.stat!(Path.join(lock_dir(key), "lock_0")).size
    assert size > 1 and rem(size, 2) == 1

    # And it is still usable afterwards.
    assert Lock.with_lock(key, fn -> :again end) == :again
  end

  defp bump_max(gauge, current) do
    max = :atomics.get(gauge, 2)

    if current > max and :atomics.compare_exchange(gauge, 2, max, current) != :ok do
      bump_max(gauge, current)
    end
  end

  defp unique_key do
    "#{__MODULE__}.#{System.unique_integer([:positive])}"
  end

  defp lock_dir(key) do
    hash = key |> :erlang.md5() |> Base.url_encode64(padding: false)
    Path.join([System.tmp_dir!(), "mix_lock_user#{Mix.Utils.detect_user_id!()}", hash])
  end

  defp await_monitors([]), do: :ok

  defp await_monitors(refs) do
    receive do
      {:DOWN, ref, _, _, _} -> await_monitors(refs -- [ref])
    end
  end
end
