# Signature-conformance fuzzer for the type checker's hardcoded remote
# signatures (Module.Types.Apply).
#
# Why this exists
# ---------------
# Module.Types.Apply carries a hand-written table of ~143 strong signatures
# for :erlang BIFs, Map/Tuple/:maps/:binary/... functions. The checker trusts
# them completely. Two staleness/wrongness modes produce user-facing FALSE
# POSITIVES:
#   * RETURN TYPE TOO NARROW: a real call returns a value outside the claimed
#     return type -- every downstream use of the result is then checked
#     against a wrong type (this is how the stale __info__(:struct) signature
#     bug manifested).
#   * DOMAIN TOO NARROW: a call the function actually accepts is outside the
#     claimed domain -- the checker warns "expected one of ..." on working
#     code.
# Both are checked EXECUTABLY here: enumerate the table, rejection-sample
# concrete argument values inside (and outside) the claimed domains, call the
# real functions, and check results against the claimed types using the same
# term-membership model the other harnesses use (kind tokens are exact at
# descr granularity).
#
# The reverse direction -- in-domain calls that RAISE (domain too wide) --
# only weakens warnings (false-negative direction), so it is reported as INFO
# and does not fail the run.
#
# Safety: calls run in short-lived Tasks with a timeout; side-effectful BIFs
# (halt/exit/spawn/send/ports/registration/code loading/...) are denylisted.
#
# How to run
# ----------
#     bin/elixir lib/elixir/scripts/sig_conformance.exs
#     bin/elixir lib/elixir/scripts/sig_conformance.exs --seed 3 --rounds 60 --info
#
# Deterministic per --seed. Exits non-zero on hard findings only.

import Module.Types.Descr

defmodule Args do
  def parse(argv), do: parse(argv, %{seed: 1, rounds: 40, info: false})

  defp parse([], acc), do: acc
  defp parse(["--seed", v | rest], acc), do: parse(rest, %{acc | seed: String.to_integer(v)})
  defp parse(["--rounds", v | rest], acc), do: parse(rest, %{acc | rounds: String.to_integer(v)})
  defp parse(["--info" | rest], acc), do: parse(rest, %{acc | info: true})
  defp parse([other | _], _), do: raise("unknown arg: #{other}")
end

# ---------------------------------------------------------------------------
# Membership of real Elixir terms in descrs
# ---------------------------------------------------------------------------
#
# Exact at descr granularity for atoms, numbers, binaries/bitstrings,
# pids/ports/refs, tuples, atom-keyed maps and (im)proper lists (via the
# :list BDD, as in descr_fuzz). Function values and non-atom-keyed maps are
# only kind-checked -> {:weak, boolean}; callers may treat weak results as
# unverifiable.

defmodule TermMember do
  import Module.Types.Descr

  def member?(v, t) do
    case strength(v) do
      :exact -> {:exact, check(v, t)}
      :weak -> {:weak, check(v, t)}
    end
  end

  defp strength(v) when is_function(v), do: :weak

  defp strength(v) when is_map(v) do
    if Enum.all?(v, fn {k, w} -> is_atom(k) and strength(w) == :exact end),
      do: :exact,
      else: :weak
  end

  defp strength(v) when is_tuple(v) do
    if Enum.all?(Tuple.to_list(v), &(strength(&1) == :exact)), do: :exact, else: :weak
  end

  defp strength([]), do: :exact

  defp strength(v) when is_list(v) do
    {elems, term} = decompose(v)
    if Enum.all?([term | elems], &(strength(&1) == :exact)), do: :exact, else: :weak
  end

  defp strength(_), do: :exact

  defp check(v, t) do
    cond do
      t == :term -> true
      not is_map(t) -> throw({:unverifiable, "non-map descr"})
      is_map_key(t, :dynamic) -> check(v, Map.fetch!(t, :dynamic))
      is_list(v) and v != [] -> list_member?(v, t)
      true -> subtype?(single(v), t)
    end
  end

  defp list_member?(v, t) do
    case t do
      %{list: bdd} ->
        {elems, terminator} = decompose(v)
        eval_bdd(bdd, elems, terminator)

      %{} ->
        false
    end
  end

  defp eval_bdd(:bdd_top, _e, _t), do: true
  defp eval_bdd(:bdd_bot, _e, _t), do: false
  defp eval_bdd({_h, elem, last}, e, t), do: literal(elem, last, e, t)

  defp eval_bdd({_h, {_lh, elem, last}, c, u, d}, e, t) do
    if literal(elem, last, e, t) do
      eval_bdd(c, e, t) or eval_bdd(u, e, t)
    else
      eval_bdd(u, e, t) or eval_bdd(d, e, t)
    end
  end

  defp eval_bdd(other, _e, _t), do: throw({:unverifiable, "unknown BDD node #{inspect(other)}"})

  defp literal(elem, last, elems, terminator) do
    Enum.all?(elems, &check(&1, elem)) and check(terminator, last)
  end

  defp decompose([h | t]) when is_list(t) and t != [] do
    {elems, terminator} = decompose(t)
    {[h | elems], terminator}
  end

  defp decompose([h | t]) when t == [], do: {[h], []}
  defp decompose([h | t]), do: {[h], t}

  def single(v) when is_boolean(v), do: atom([v])
  def single(v) when is_atom(v), do: atom([v])
  def single(v) when is_integer(v), do: integer()
  def single(v) when is_float(v), do: float()
  def single(v) when is_binary(v), do: binary()
  def single(v) when is_bitstring(v), do: opt_difference(bitstring(), binary())
  def single(v) when is_pid(v), do: pid()
  def single(v) when is_port(v), do: port()
  def single(v) when is_reference(v), do: reference()
  def single([]), do: empty_list()
  def single(v) when is_function(v), do: fun(:erlang.fun_info(v)[:arity])
  def single(v) when is_tuple(v), do: tuple(Enum.map(Tuple.to_list(v), &single/1))

  def single(v) when is_map(v) and not is_struct(v) do
    if Enum.all?(Map.keys(v), &is_atom/1) do
      closed_map(Enum.map(v, fn {k, w} -> {k, single(w)} end))
    else
      # descr models non-atom keys via domains; over-approximate as open map
      throw({:unverifiable, "non-atom-keyed map"})
    end
  end

  def single(v), do: throw({:unverifiable, "unencodable term #{inspect(v)}"})
end

# ---------------------------------------------------------------------------
# Signature table extraction + call safety
# ---------------------------------------------------------------------------

defmodule Table do
  def mfas do
    # After an in-VM reload (canary runs), :code.which no longer points at a
    # file; fall back to the shipped beam, which has the same clause heads.
    beam =
      case :code.which(Module.Types.Apply) do
        path when is_list(path) and path != [] ->
          path

        _ ->
          ~c"#{:code.lib_dir(:elixir)}/ebin/Elixir.Module.Types.Apply.beam"
      end

    {:ok, {_, [abstract_code: {:raw_abstract_v1, forms}]}} =
      :beam_lib.chunks(beam, [:abstract_code])

    for {:function, _, :signature, 3, cls} <- forms,
        {:clause, _, [{:atom, _, m}, {:atom, _, f}, {:integer, _, a}], [], _} <- cls,
        uniq: true,
        do: {m, f, a}
  end

  # Side-effectful / environment-touching functions we refuse to call, plus
  # known-intentional signature divergences.
  @deny [
    {:erlang, :halt},
    {:erlang, :exit},
    {:erlang, :throw},
    {:erlang, :error},
    {:erlang, :spawn},
    {:erlang, :spawn_link},
    {:erlang, :spawn_monitor},
    {:erlang, :send},
    {:erlang, :send_after},
    {:erlang, :port_command},
    {:erlang, :open_port},
    {:erlang, :register},
    {:erlang, :unregister},
    {:erlang, :link},
    {:erlang, :unlink},
    {:erlang, :monitor},
    {:erlang, :demonitor},
    {:erlang, :process_flag},
    {:erlang, :group_leader},
    {:erlang, :garbage_collect},
    {:erlang, :load_module},
    {:erlang, :delete_module},
    {:erlang, :purge_module},
    {:erlang, :binary_to_term},
    {:erlang, :binary_to_atom},
    {:erlang, :binary_to_existing_atom},
    {:erlang, :list_to_atom},
    {:erlang, :list_to_existing_atom},
    {:erlang, :apply},
    {:erlang, :alias},
    {:erlang, :unalias},
    {:erlang, :cancel_timer},
    {:erlang, :suspend_process},
    {:erlang, :resume_process},
    # forward-compat signature for a BIF newer OTP adds (documented in
    # BUGS_FABLE.txt N4) -- calling it on older OTP is meaningless
    {:erlang, :is_integer},
    # deprecated module-argument form prints runtime warnings when probed
    {Map, :from_struct},
    # KNOWN-INTENTIONAL domain narrowness: :erlang.raise/3 with an invalid
    # class RETURNS the atom :badarg instead of raising (documented OTP
    # behavior), so the :error|:exit|:throw domain is technically too narrow.
    # The checker treats a non-literal class as a bug worth warning about --
    # a deliberate lint. Found by this tool, triaged 2026-07-03.
    {:erlang, :raise}
  ]

  def denied?({m, f, _a}), do: {m, f} in @deny

  def signature(m, f, a), do: Module.Types.Apply.signature(m, f, a)
end

defmodule Pool do
  # Candidate concrete values for rejection sampling. Deterministic.
  def values do
    [
      :x,
      :ok,
      :error,
      :infinity,
      :undefined,
      true,
      false,
      nil,
      0,
      1,
      -1,
      2,
      3,
      17,
      255,
      1_000_003,
      -42,
      0.0,
      1.5,
      -3.25,
      "",
      "a",
      "hello",
      <<0, 255>>,
      <<3::3>>,
      <<1::1>>,
      [],
      [1, 2, 3],
      [:x, :y],
      ["a", 1],
      [1 | 2],
      ~c"abc",
      {},
      {1},
      {:ok, 1},
      {1, 2, 3},
      {:x, "y", 3},
      %{},
      %{a: 1},
      %{a: 1, b: "x"},
      %{1 => :one},
      %{"k" => 1},
      self(),
      make_ref(),
      fn -> :stub0 end,
      fn _ -> :stub1 end,
      fn _, _ -> :stub2 end
    ]
  end

  # Sample a value of the pool inside `descr` (exact membership only).
  def in_descr(descr, exclude \\ []) do
    values()
    |> Enum.shuffle()
    |> Enum.find(fn v ->
      v not in exclude and
        try do
          TermMember.member?(v, descr) == {:exact, true}
        catch
          {:unverifiable, _} -> false
        end
    end)
  end

  def out_of_descr(descr) do
    values()
    |> Enum.shuffle()
    |> Enum.find(fn v ->
      try do
        TermMember.member?(v, descr) == {:exact, false}
      catch
        {:unverifiable, _} -> false
      end
    end)
  end
end

# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

defmodule Runner do
  import Module.Types.Descr

  def run(%{seed: seed, rounds: rounds, info: info?}) do
    :rand.seed(:exsss, {seed, seed * 7 + 1, seed * 13 + 3})
    mfas = Table.mfas()

    IO.puts(
      "sig_conformance: #{length(mfas)} table entries, #{rounds} rounds each, seed #{seed}\n"
    )

    {hard, infos, skipped} =
      Enum.reduce(Enum.sort(mfas), {[], [], 0}, fn mfa, {hard, infos, skipped} ->
        if Table.denied?(mfa) do
          {hard, infos, skipped + 1}
        else
          {m, f, a} = mfa
          {:strong, _domain, clauses} = Table.signature(m, f, a)
          {h, i} = check_mfa(mfa, clauses, rounds)
          {hard ++ h, infos ++ i, skipped}
        end
      end)

    report(hard, infos, skipped, info?)
  end

  defp check_mfa({m, f, a} = mfa, clauses, rounds) do
    domain_union = domain_union(clauses, a)

    {hard1, infos} =
      Enum.reduce(clauses, {[], []}, fn {arg_types, ret}, {hard, infos} ->
        Enum.reduce(1..rounds, {hard, infos}, fn _, {hard, infos} ->
          case sample_args(arg_types) do
            nil ->
              {hard, infos}

            args ->
              case call(m, f, args) do
                {:ok, result} ->
                  case verify_return(result, ret) do
                    :ok ->
                      {hard, infos}

                    :violation ->
                      finding = {:return_violation, mfa, args, result, ret}
                      {maybe_add(hard, finding), infos}

                    :unverifiable ->
                      {hard, infos}
                  end

                {:raised, kind} ->
                  {hard, maybe_add(infos, {:in_domain_raise, mfa, args, kind})}

                :timeout ->
                  {hard, maybe_add(infos, {:timeout, mfa, args})}
              end
          end
        end)
      end)

    # Out-of-domain probes: one position at a time (nullary functions have
    # no positions to probe).
    hard2 =
      Enum.reduce(0..(a - 1)//1, [], fn j, acc ->
        Enum.reduce(1..min(rounds, 15), acc, fn _, acc ->
          with args when not is_nil(args) <- sample_out_of_domain(domain_union, j) do
            case call(m, f, args) do
              {:ok, result} ->
                finding = {:domain_too_narrow, mfa, args, j, result, Enum.at(domain_union, j)}
                maybe_add(acc, finding)

              _ ->
                acc
            end
          else
            _ -> acc
          end
        end)
      end)

    {hard1 ++ hard2, infos}
  end

  defp domain_union(clauses, arity) do
    Enum.reduce(clauses, List.duplicate(none(), arity), fn {args, _ret}, acc ->
      Enum.zip_with(args, acc, &opt_union/2)
    end)
  end

  defp sample_args(arg_types) do
    args = Enum.map(arg_types, &Pool.in_descr/1)
    if Enum.any?(args, &is_nil/1), do: nil, else: args
  end

  defp sample_out_of_domain(domain_union, j) do
    args =
      domain_union
      |> Enum.with_index()
      |> Enum.map(fn {d, i} ->
        if i == j, do: Pool.out_of_descr(d), else: Pool.in_descr(d)
      end)

    if Enum.any?(args, &is_nil/1), do: nil, else: args
  end

  defp verify_return(result, ret) do
    case TermMember.member?(result, ret) do
      {:exact, true} -> :ok
      {:exact, false} -> :violation
      {:weak, true} -> :ok
      {:weak, false} -> :unverifiable
    end
  catch
    {:unverifiable, _} -> :unverifiable
  end

  defp call(m, f, args) do
    task =
      Task.async(fn ->
        try do
          {:ok, apply(m, f, args)}
        rescue
          e -> {:raised, e.__struct__}
        catch
          kind, v -> {:raised, {kind, limited(v)}}
        end
      end)

    case Task.yield(task, 1000) || Task.shutdown(task, :brutal_kill) do
      {:ok, result} -> result
      nil -> :timeout
    end
  end

  defp limited(v), do: v |> inspect(limit: 3) |> String.slice(0, 60)

  # One finding per (kind, mfa) keeps a wrong signature from flooding output.
  defp maybe_add(list, finding) do
    key = {elem(finding, 0), elem(finding, 1)}

    if Enum.any?(list, fn f -> {elem(f, 0), elem(f, 1)} == key end) do
      list
    else
      [finding | list]
    end
  end

  defp report(hard, infos, skipped, info?) do
    IO.puts("skipped #{skipped} denylisted entries; #{length(infos)} info note(s)\n")

    if info? and infos != [] do
      IO.puts("-- INFO (false-negative direction, does not fail the run) --")

      for i <- Enum.reverse(infos) do
        case i do
          {:in_domain_raise, {m, f, a}, args, kind} ->
            IO.puts(
              "in-domain raise: #{inspect(m)}.#{f}/#{a} #{inspect(args, limit: 5)} -> #{inspect(kind)}"
            )

          {:timeout, {m, f, a}, args} ->
            IO.puts("timeout: #{inspect(m)}.#{f}/#{a} #{inspect(args, limit: 5)}")
        end
      end

      IO.puts("")
    end

    case Enum.reverse(hard) do
      [] ->
        IO.puts("PASS -- no return-type or domain-narrowness violations.")
        System.halt(0)

      hard ->
        IO.puts("FAIL -- #{length(hard)} hard finding(s):\n")

        for finding <- hard do
          case finding do
            {:return_violation, {m, f, a}, args, result, ret} ->
              IO.puts("* RETURN TYPE VIOLATION #{inspect(m)}.#{f}/#{a}")

              IO.puts(
                "    call:     #{inspect(m)}.#{f}(#{Enum.map_join(args, ", ", &inspect/1)})"
              )

              IO.puts("    returned: #{inspect(result, limit: 10)}")
              IO.puts("    claimed:  #{to_quoted_string(ret)}")

            {:domain_too_narrow, {m, f, a}, args, j, result, dj} ->
              IO.puts("* DOMAIN TOO NARROW #{inspect(m)}.#{f}/#{a} (arg #{j})")

              IO.puts(
                "    call:     #{inspect(m)}.#{f}(#{Enum.map_join(args, ", ", &inspect/1)})"
              )

              IO.puts(
                "    returned: #{inspect(result, limit: 10)} (checker would warn on this call)"
              )

              IO.puts("    claimed domain for arg #{j}: #{to_quoted_string(dj)}")
          end

          IO.puts("")
        end

        System.halt(1)
    end
  end
end

Runner.run(Args.parse(System.argv()))
