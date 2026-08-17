# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

defmodule Mix.Sync.Lock do
  @moduledoc false

  # Lock implementation working across multiple OS processes.
  #
  # The lock is implemented using TCP sockets and hard links.
  #
  # A process holds the lock if it owns a TCP socket, whose port is
  # written in the lock_0 file. We need to create such lock files
  # atomically, so the process first writes its port to a port_P
  # file and then attempts to create a hard link to it at lock_0.
  #
  # An inherent problem with lock files is that the lock owner may
  # terminate abruptly, leaving a "stale" file. Other processes can
  # detect a stale file by reading the port written in that file,
  # trying to connect to that port and failing. In order for another
  # process to link to the same path, the file needs to be replaced.
  # However, we need to guarantee that only a single process can
  # remove or replace the file, otherwise a concurrent process may
  # end up removing a newly linked file.
  #
  # To address this problem we employ a chained locking procedure.
  # Specifically, we attempt to link our port to lock_0, if that
  # fails, we try to connect to the lock_0 port. If we manage to
  # connect, it means the lock is taken, so we wait for it to close
  # and start over. If we fail to connect, it means the lock is stale,
  # so we want to replace it. In order to do that, we try to obtain
  # lock_1. Again, we try to link and connect. Eventually, we should
  # successfully link to lock_N. At that point we can clean up all
  # the files, so we perform these steps:
  #
  #   * replace lock_0 content with port P
  #   * remove all port_P files
  #   * remove all lock_1+ files
  #
  # It is important to perform these steps in this order, to avoid
  # race conditions. By moving to lock_0, we make sure that all new
  # processes trying to lock will connect to our port. By removing
  # all port_P files we make sure that currently paused processes
  # that are about to link port_P at lock_N will fail to link, since
  # the port_P file will no longer exist (once lock_N is removed).
  #
  # Finally, note that we do not remove the lock file in `unlock/1`.
  # If we did that, another process could read it before removal,
  # then it may connect and fail (once the socket is closed), in such
  # case the process would assume the file is stale and needs to be
  # replaced, therefore possibly replacing another process who
  # successfully links at the empty spot. This means we effectively
  # always leave a stale file, however, in order to shortcut the port
  # check for future processes, we atomically replace the file content
  # with port 0, to indicate the file is stale.
  #
  # The main caveat of using ephemeral TCP ports is that they are not
  # unique. This creates a theoretical scenario where the lock holder
  # terminates abruptly and leaves its port in lock_0, then the port
  # is assigned to a unrelated process (unaware of the locking). To
  # handle this scenario, when we connect to a lock_N port, we expect
  # it to immediately send us `@probe_data`. If this does not happen
  # within `@probe_timeout_ms`, we assume the port is taken by an
  # unrelated process and the lock file is stale. Note that it is ok
  # to use a long timeout, because this scenario is very unlikely.
  # Theoretically, if an actual lock owner is not able to send the
  # probe data within the timeout, the lock will fail, however with
  # a high enough timeout, this should not be a problem in practice.

  @loopback {127, 0, 0, 1}
  @listen_opts [:binary, ip: @loopback, packet: :raw, nodelay: true, backlog: 128, active: false]
  @connect_opts [:binary, packet: :raw, nodelay: true, active: false]
  @probe_data "mixlock"
  @probe_data_size byte_size(@probe_data)
  @probe_timeout_ms 5_000

  @typedoc """
  Options for `with_lock/3`.
  """
  @type with_lock_opts :: [
          on_taken: (String.t() -> any())
        ]

  @doc """
  Acquires a lock identified by the given key.

  This function blocks until the lock is acquired by this process,
  and then executes `fun`, returning its return value.

  This function can also be called if this process already has the
  lock. In such case the function is executed immediately.

  When the `MIX_OS_CONCURRENCY_LOCK` environment variable is set to
  a falsy value, the lock is ignored and the function is executed
  immediately.

  ## Options

    * `:on_taken` - a one-arity function called if the lock is held
      by a different process. The operating system PID of that process
      is given as the first argument (as a string). This function may
      be called multiple times, if the lock owner changes, until it
      is successfully acquired by this process.

  """
  @spec with_lock(iodata(), (-> term()), with_lock_opts()) :: term()
  def with_lock(key, fun, opts \\ []) do
    opts = Keyword.validate!(opts, [:on_taken])

    hash = key |> :erlang.md5() |> Base.url_encode64(padding: false)
    path = Path.join(base_path(), hash)

    pdict_key = {__MODULE__, path}
    has_lock? = Process.get(pdict_key, false)

    if has_lock? or lock_disabled?() do
      fun.()
    else
      lock = lock(path, opts[:on_taken])
      Process.put(pdict_key, true)

      try do
        fun.()
      after
        # Unlocking will always close the socket, but it may raise,
        # so we remove key from the dictionary first
        Process.delete(pdict_key)
        unlock(lock)
      end
    end
  end

  defp base_path do
    # We include user in the dir to avoid permission conflicts across users
    Path.join(System.tmp_dir!(), "mix_lock_user#{Mix.Utils.detect_user_id!()}")
  end

  defp lock_disabled?(), do: System.get_env("MIX_OS_CONCURRENCY_LOCK") in ~w(0 false)

  defp lock(path, on_taken) do
    File.mkdir_p!(path)

    case listen() do
      {:ok, socket, port} ->
        spawn_link(fn -> accept_loop(socket) end)

        try do
          try_lock(path, socket, port, on_taken)
        rescue
          exception ->
            # Close the socket to make sure we don't block the lock
            :gen_tcp.close(socket)
            reraise exception, __STACKTRACE__
        end

      {:error, reason} ->
        Mix.raise("failed to acquire filesystem lock using TCP, reason: #{inspect(reason)}")
    end
  end

  defp listen do
    with {:ok, socket} <- :gen_tcp.listen(0, @listen_opts) do
      case :inet.port(socket) do
        {:ok, port} ->
          {:ok, socket, port}

        {:error, reason} ->
          :gen_tcp.close(socket)
          {:error, reason}
      end
    end
  end

  defp try_lock(path, socket, port, on_taken) do
    port_path = Path.join(path, "port_#{port}")
    os_pid = System.pid()

    switch_file_create!(port_path, encode_lock_info(port, os_pid))

    case grab_lock(path, port_path, port, 0) do
      {:ok, 0} ->
        # We grabbed lock_0, so all good
        %{socket: socket, path: path}

      {:ok, _n} ->
        # We grabbed lock_1+, so we need to replace lock_0 and clean up
        take_over(path, port, os_pid)
        %{socket: socket, path: path}

      {:taken, probe_socket, os_pid} ->
        # Another process has the lock, wait for close and start over
        if on_taken, do: on_taken.(os_pid)
        await_close(probe_socket)
        try_lock(path, socket, port, on_taken)

      :invalidated ->
        try_lock(path, socket, port, on_taken)
    end
  end

  defp grab_lock(path, port_path, own_port, n) do
    lock_path = Path.join(path, "lock_#{n}")

    case File.ln(port_path, lock_path) do
      :ok ->
        {:ok, n}

      {:error, :eexist} ->
        case probe(lock_path, own_port) do
          {:ok, probe_socket, os_pid} ->
            {:taken, probe_socket, os_pid}

          {:error, _reason} ->
            grab_lock(path, port_path, own_port, n + 1)
        end

      {:error, :enoent} ->
        :invalidated

      {:error, reason} ->
        Mix.raise("""
        could not create hard link from #{port_path} to "#{lock_path}: #{:file.format_error(reason)}.

        Hard link support is required for Mix compilation locking. If your system \
        does not support hard links, set MIX_OS_CONCURRENCY_LOCK=0\
        """)
    end
  end

  defp accept_loop(listen_socket) do
    case accept(listen_socket) do
      {:ok, socket} ->
        _ = :gen_tcp.send(socket, @probe_data)
        accept_loop(listen_socket)

      {:error, reason} when reason in [:closed, :einval] ->
        :ok

      {:error, reason} ->
        raise RuntimeError,
              "failed to accept connection in #{inspect(__MODULE__)}.receive_event/1, reason: #{inspect(reason)}"
    end
  end

  defp probe(port_path, own_port) do
    with {:ok, port, os_pid} <- fetch_probe_port(port_path, own_port),
         {:ok, socket} <- connect(port),
         {:ok, socket} <- await_probe_data(socket) do
      {:ok, socket, os_pid}
    end
  end

  @doc false
  def fetch_probe_port(port_path, own_port) do
    case switch_file_read(port_path) do
      {:ok, data} ->
        case decode_lock_info(data) do
          {0, _os_pid} ->
            {:error, :ignore}

          # A lock file naming our own listening port must be a stale
          # leftover, for example from an interrupted take_over/3 followed
          # by the OS recycling the port. No other live process can own the
          # port we are listening on, so connecting would mean connecting
          # to ourselves and waiting on our own socket forever.
          {^own_port, _os_pid} ->
            {:error, :own_port}

          {port, os_pid} ->
            {:ok, port, os_pid}

          :error ->
            {:error, :invalid}
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp connect(port) do
    # On Windows connecting to an unbound port takes a few seconds to
    # fail, so instead we shortcut the check by attempting a listen,
    # which succeeds or fails immediately. Note that `reuseaddr` here
    # ensures that if the listening socket closed recently, we can
    # immediately reclaim the same port.
    case :gen_tcp.listen(port, [reuseaddr: true] ++ @listen_opts) do
      {:ok, socket} ->
        :gen_tcp.close(socket)
        # The port is free, so connecting would fail
        {:error, :econnrefused}

      {:error, _reason} ->
        :gen_tcp.connect(@loopback, port, @connect_opts)
    end
  end

  defp await_probe_data(socket) do
    case recv(socket, @probe_data_size, @probe_timeout_ms) do
      {:ok, @probe_data} ->
        {:ok, socket}

      {:ok, _data} ->
        :gen_tcp.close(socket)
        {:error, :unexpected_port_owner}

      {:error, reason} ->
        :gen_tcp.close(socket)
        {:error, reason}
    end
  end

  defp recv(socket, size, timeout \\ :infinity) do
    # eintr is "Interrupted system call".
    with {:error, :eintr} <- :gen_tcp.recv(socket, size, timeout) do
      recv(socket, size, timeout)
    end
  end

  defp accept(socket) do
    with {:error, :eintr} <- :gen_tcp.accept(socket) do
      accept(socket)
    end
  end

  defp take_over(path, port, os_pid) do
    # The operations here must happen in precise order, so if anything
    # fails, we keep the files as is and the next process that grabs
    # the lock will do the cleanup

    lock_path = Path.join(path, "lock_0")

    switch_file_replace!(lock_path, encode_lock_info(port, os_pid))

    names = File.ls!(path)

    # On Windows, removing a file may fail if the file is open, so we
    # ignore failures just to be safe

    for "port_" <> _ = name <- names do
      _ = File.rm(Path.join(path, name))
    end

    for "lock_" <> _ = name <- names, name != "lock_0" do
      _ = File.rm(Path.join(path, name))
    end
  end

  defp await_close(socket) do
    case recv(socket, 0) do
      {:error, :closed} ->
        :ok

      {:error, _other} ->
        # In case of an unexpected error, we close the socket ourselves
        # to retry
        :gen_tcp.close(socket)
    end
  end

  defp unlock(lock) do
    lock_path = Path.join(lock.path, "lock_0")

    switch_file_replace!(lock_path, encode_lock_info(0, ""))
  after
    # Closing the socket will cause the accepting process to finish
    # and all accepted sockets (tied to that process) will get closed
    :gen_tcp.close(lock.socket)
  end

  @doc false
  def encode_lock_info(port, os_pid) do
    os_pid_size = byte_size(os_pid)

    if os_pid_size > 32 do
      Mix.raise("unexpectedly long PID: #{inspect(os_pid)}")
    end

    # The info needs to have fixed size, so we pad os_pid to maximum
    # of 32 bytes (we expect it to be a few bytes).
    padding_size = 32 - os_pid_size
    padding = :binary.copy(<<0>>, padding_size)

    <<
      port::unsigned-integer-32,
      padding_size::unsigned-integer-8,
      padding::binary,
      os_pid::binary
    >>
  end

  # Valid encoded lock info always has a fixed size: 4 bytes of port,
  # 1 byte of padding size and 32 bytes of padding plus PID, 37 in total.
  # The guard rejects shorter or longer content that happens to match the
  # variable-sized binary pattern, so we never probe a port decoded from
  # a file of the wrong size.
  @doc false
  def decode_lock_info(data) do
    case data do
      <<
        port::unsigned-integer-32,
        padding_size::unsigned-integer-8,
        _padding::binary-size(padding_size),
        os_pid::binary
      >>
      when padding_size + byte_size(os_pid) == 32 ->
        {port, os_pid}

      # Malformed content (e.g. from an interrupted writer or an older
      # version). Treat as stale rather than crashing the caller.
      _ ->
        :error
    end
  end

  # We need a mechanism to atomically replace file content. Typically,
  # we could use File.rename/2 to do that, however File.rename/2 is
  # not atomic on Windows, if the destination exists [1].
  #
  # As an alternative approach we use a switch-file. The file content
  # consists of 1 switch byte (either 0 or 1) and two content segments
  # with fixed, equal lengths. The switch byte indicates which segment
  # is currently active. To replace the file content, we write to the
  # non-active segment, then we toggle the switch byte. While we cannot
  # write multiple bytes atomically (since they may reside in multiple
  # disk sectors), if we toggle only a single byte, there is no
  # intermediate invalid state, which gives us the atomic replace we
  # need.
  #
  # Note that file content can be replaced only by a single process
  # at a time.
  #
  # [1]: https://github.com/elixir-lang/elixir/pull/14793#issuecomment-3338665065
  @doc false
  def switch_file_create!(path, content) do
    # We must never open this path with truncation if it may already exist,
    # because it can be hard-linked into lock_0. The lock protocol links a
    # process's port_P file at lock_0 (see grab_lock/4) and, on unlock,
    # deliberately leaves both names in place (see the note above unlock/1).
    # When the operating system later recycles the ephemeral port P, a new
    # process computes the same "port_P" name that the stale file still holds.
    # Opening it with :write would O_TRUNC the shared inode, momentarily
    # emptying lock_0 and then overwriting it with this process's own port -
    # which corrupts concurrent readers, poisons the lock for future callers
    # if we die mid-write, and (since we then read our own port back) makes us
    # connect to ourselves and deadlock.
    #
    # Unlinking the name first guarantees we always write to a fresh inode.
    # Removing the name never affects lock_0: it only drops the extra hard
    # link, leaving lock_0 pointing at the original inode with its content
    # intact. The port_P name is effectively owned by whoever currently holds
    # the TCP port P, and that is us, so there is no concurrent writer to race.
    #
    # We must not ignore a removal failure: if the stale name could not be
    # unlinked, File.write! below would open and O_TRUNC the existing inode -
    # exactly the corruption we are preventing - so we fail loudly instead.
    case File.rm(path) do
      :ok -> :ok
      {:error, :enoent} -> :ok
      {:error, reason} -> raise File.Error, reason: reason, action: "remove file", path: path
    end

    data = <<0, content::binary, content::binary>>
    File.write!(path, data, [:raw])
  end

  defp switch_file_replace!(path, new_content) do
    file = File.open!(path, [:read, :write, :binary, :raw])

    content_size = byte_size(new_content)
    expected_size = 1 + 2 * content_size

    try do
      switch_byte =
        case :file.read(file, 1) do
          {:ok, <<byte>>} when byte in [0, 1] -> byte
          _ -> nil
        end

      file_size =
        case :file.position(file, :eof) do
          {:ok, size} -> size
          _ -> nil
        end

      if switch_byte != nil and file_size == expected_size do
        # A well-formed switch-file: stage the new content in the inactive
        # segment, then flip the single switch byte. Toggling one byte is the
        # atomic replace (see the note above this section).
        inactive_content_position =
          case switch_byte do
            0 -> 1 + content_size
            1 -> 1
          end

        file_pwrite!(file, inactive_content_position, new_content)
        file_pwrite!(file, 0, <<1 - switch_byte>>)
      else
        # The file is empty, truncated, or otherwise malformed (an interrupted
        # writer, or a file from an older version). There is no valid inactive
        # segment to stage into, so the atomic toggle cannot be used. We own
        # the lock, either directly or through the chained takeover, so we
        # repair the file IN PLACE through this descriptor.
        #
        # We deliberately do NOT unlink and recreate it: removing lock_0 would
        # let a concurrent contender link its own port file at the now-free
        # name and consider the lock acquired (the removal race the chained
        # protocol is designed to avoid). Rewriting the whole switch-file in
        # place, and truncating to its exact size, cannot corrupt a well-formed
        # file - it only runs when the file is already malformed, a state
        # readers already treat as stale.
        file_pwrite!(file, 0, <<0, new_content::binary, new_content::binary>>)
        {:ok, _} = :file.position(file, expected_size)
        :ok = :file.truncate(file)
      end
    after
      File.close(file)
    end
  end

  @doc false
  def switch_file_read(path) do
    with {:ok, data} <- File.read(path) do
      case data do
        <<switch_byte, rest::binary>>
        when switch_byte in [0, 1] and byte_size(rest) > 0 and rem(byte_size(rest), 2) == 0 ->
          content_size = div(byte_size(rest), 2)
          <<content1::binary-size(^content_size), content2::binary-size(^content_size)>> = rest
          content = if switch_byte == 0, do: content1, else: content2
          {:ok, content}

        # Empty or otherwise malformed switch-file. This can happen if a writer
        # was interrupted mid-write (leaving 0 bytes) or the file predates this
        # version. Report it as invalid so callers treat the lock as stale and
        # take it over, instead of raising a MatchError.
        _ ->
          {:error, :invalid}
      end
    end
  end

  defp file_pwrite!(file, position, bytes) do
    case :file.pwrite(file, position, bytes) do
      :ok ->
        :ok

      {:error, reason} ->
        raise File.Error, reason: reason, action: "write to file at position"
    end
  end
end
