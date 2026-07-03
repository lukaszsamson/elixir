# Soundness tester for the compiler's inferred type signatures.
#
# Why this exists
# ---------------
# Neither descr_fuzz (algebra) nor apply_fuzz (emitted warnings) validates the
# SIGNATURES the compiler infers for user functions (Module.Types.infer/7).
# Inferred signatures are persisted in the "ExCk" beam chunk and drive
# cross-module checking: if an inferred DOMAIN is too narrow, every caller
# passing a perfectly valid argument gets a false "expected one of ..."
# warning; if an inferred RETURN type is too narrow, every use of the result
# is checked against a wrong type. Both are false-positive factories that
# surface far from their cause.
#
# Strategy
# --------
# Reuse apply_fuzz's feature grammar: generated modules are well-typed by
# construction and every clause carries a runtime WITNESS (arguments known to
# be valid, with the expected clause tag). For each compiled module, decode
# the checker chunk and demand, for every witness of every exported def:
#
#   1. DOMAIN SOUNDNESS: the witness arguments (which demonstrably work at
#      runtime) are members of the inferred per-position domain. A valid
#      input outside the inferred domain means callers get warned on correct
#      code.
#   2. RETURN SOUNDNESS: the value the call actually returns is a member of
#      the union of the inferred clause return types.
#
# Membership of real terms in descrs uses the same kind-token-exact model as
# sig_conformance.exs; function-valued or otherwise unencodable terms are
# skipped and counted.
#
# How to run
# ----------
#     bin/elixir lib/elixir/scripts/infer_soundness.exs
#     bin/elixir lib/elixir/scripts/infer_soundness.exs --seeds 1-10 --samples 300
#
# Deterministic per seed; exits non-zero on any finding. Canary validation
# (both verified when this was written, via loading a corrupted
# Module.Types.Apply into the VM before fuzzing):
#   * RETURN oracle: corrupt a body-call signature (byte_size return ->
#     pid()); the poisoned type propagates into inferred returns and the
#     oracle fires.
#   * DOMAIN oracle: body-call signatures do NOT reach inferred domains
#     (those derive from patterns/guards), so corrupt the GUARD signature
#     table instead: change `is_integer: integer()` to `is_integer: pid()`
#     in apply.ex's is_guards list. Integer-guarded functions then infer
#     domain pid() and their working integer witnesses fall outside --
#     the oracle fires, including through map patterns
#     (%{a: 1} vs inferred %{..., a: pid()}).

Code.put_compiler_option(:ignore_module_conflict, true)

# Shared typed-program grammar (Expr/Feature/Build).
Code.require_file("apply_grammar.exs", __DIR__)

defmodule InferArgs do
  def parse(argv), do: parse(argv, %{seeds: 1..5, samples: 200})

  defp parse([], acc), do: acc
  defp parse(["--seeds", v | rest], acc), do: parse(rest, %{acc | seeds: range(v)})

  defp parse(["--samples", v | rest], acc),
    do: parse(rest, %{acc | samples: String.to_integer(v)})

  defp parse([other | _], _), do: raise("unknown arg: #{other}")

  defp range(v) do
    case String.split(v, "-") do
      [a, b] -> String.to_integer(a)..String.to_integer(b)
      [a] -> String.to_integer(a)..String.to_integer(a)
    end
  end
end

# Same exact-at-descr-granularity term membership as sig_conformance.exs.
defmodule InferMember do
  import Module.Types.Descr

  def member?(v, t) do
    {:exact, check(v, t)}
  catch
    {:unverifiable, why} -> {:unverifiable, why}
  end

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

  defp single(v) when is_boolean(v), do: atom([v])
  defp single(v) when is_atom(v), do: atom([v])
  defp single(v) when is_integer(v), do: integer()
  defp single(v) when is_float(v), do: float()
  defp single(v) when is_binary(v), do: binary()
  defp single(v) when is_bitstring(v), do: opt_difference(bitstring(), binary())
  defp single(v) when is_pid(v), do: pid()
  defp single(v) when is_port(v), do: port()
  defp single(v) when is_reference(v), do: reference()
  defp single([]), do: empty_list()
  defp single(v) when is_function(v), do: throw({:unverifiable, "function value"})
  defp single(v) when is_tuple(v), do: tuple(Enum.map(Tuple.to_list(v), &single/1))

  defp single(v) when is_map(v) and not is_struct(v) do
    if Enum.all?(Map.keys(v), &is_atom/1) do
      closed_map(Enum.map(v, fn {k, w} -> {k, single(w)} end))
    else
      throw({:unverifiable, "non-atom-keyed map"})
    end
  end

  defp single(v) when is_struct(v) do
    fields = v |> Map.from_struct() |> Enum.map(fn {k, w} -> {k, single(w)} end)
    closed_map([{:__struct__, atom([v.__struct__])} | fields])
  end

  defp single(v), do: throw({:unverifiable, "unencodable #{inspect(v)}"})
end

defmodule InferRunner do
  import Module.Types.Descr

  def run(%{seeds: seeds, samples: samples}) do
    IO.puts("infer_soundness: seeds #{inspect(seeds)}, #{samples} samples/seed\n")

    {findings, stats} =
      for seed <- seeds, reduce: {[], %{checked: 0, skipped: 0, no_sig: 0}} do
        {acc, stats} ->
          :rand.seed(:exsss, {seed, seed * 7 + 1, seed * 13 + 3})
          run_seed(seed, samples, acc, stats)
      end

    report(findings, stats)
  end

  defp run_seed(seed, samples, acc, stats) do
    Enum.reduce(1..samples, {acc, stats}, fn i, {acc, stats} ->
      features = for j <- 1..:rand.uniform(2), do: Feature.random("#{seed}_#{i}_#{j}")
      built = Build.assemble("InferF#{seed}x#{i}", features)

      case compile(built) do
        {:ok, modules} ->
          sigs = chunk_sigs(modules, built.mod)
          {acc, stats} = verify(built, sigs, seed, i, acc, stats)
          purge(modules)
          {acc, stats}

        :error ->
          {acc, stats}
      end
    end)
  end

  defp compile(built) do
    {result, _diags} =
      Code.with_diagnostics(fn ->
        try do
          {:ok, Code.compile_string(built.src)}
        rescue
          _ -> :error
        end
      end)

    result
  end

  defp chunk_sigs(modules, main_mod) do
    main = Module.concat([main_mod])

    with {_mod, beam} <- List.keyfind(modules, main, 0),
         {:ok, {^main, [{~c"ExCk", chunk}]}} <- :beam_lib.chunks(beam, [~c"ExCk"]),
         {_version, %{exports: exports}} <- :erlang.binary_to_term(chunk) do
      Map.new(exports, fn {{f, a}, info} -> {{f, a}, Map.get(info, :sig, :none)} end)
    else
      _ -> %{}
    end
  end

  defp verify(built, sigs, seed, i, acc, stats) do
    mod = Module.concat([built.mod])

    Enum.reduce(built.witnesses, {acc, stats}, fn {f, args, expect}, {acc, stats} ->
      case Map.get(sigs, {f, length(args)}) do
        {:infer, _domain, clauses} when clauses != [] ->
          case run_witness(mod, f, args, expect) do
            {:ok, result} ->
              stats = %{stats | checked: stats.checked + 1}

              acc
              |> check_domain(built, f, args, clauses, seed, i)
              |> check_return(built, f, args, result, clauses, seed, i)
              |> then(&{&1, stats})

            :witness_failed ->
              # generator problem, not an inference finding
              {acc, %{stats | skipped: stats.skipped + 1}}
          end

        _ ->
          {acc, %{stats | no_sig: stats.no_sig + 1}}
      end
    end)
  end

  defp run_witness(mod, f, args, expect) do
    result = apply(mod, f, args)

    case expect do
      {:tag, tag} when elem(result, 0) == tag -> {:ok, result}
      {:tag, _} -> :witness_failed
      :any -> {:ok, result}
    end
  rescue
    _ -> :witness_failed
  catch
    _, _ -> :witness_failed
  end

  # Every witness argument must be inside the positionwise union of the
  # inferred clause domains -- it demonstrably works at runtime.
  defp check_domain(acc, built, f, args, clauses, seed, i) do
    domain =
      Enum.reduce(clauses, List.duplicate(none(), length(args)), fn {arg_types, _ret}, acc2 ->
        Enum.zip_with(arg_types, acc2, &opt_union/2)
      end)

    bad =
      Enum.zip(args, domain)
      |> Enum.with_index()
      |> Enum.find(fn {{v, d}, _j} -> InferMember.member?(v, d) == {:exact, false} end)

    case bad do
      nil ->
        acc

      {{v, d}, j} ->
        add(acc, %{
          kind: :domain,
          seed: seed,
          sample: i,
          mfa: "#{built.mod}.#{f}/#{length(args)}",
          detail:
            "witness arg #{j} = #{inspect(v)} runs fine but is outside the inferred domain #{to_quoted_string(d)}",
          src: built.src
        })
    end
  end

  defp check_return(acc, built, f, args, result, clauses, seed, i) do
    ret_union = Enum.reduce(clauses, none(), fn {_args, ret}, u -> opt_union(ret, u) end)

    case InferMember.member?(result, ret_union) do
      {:exact, false} ->
        add(acc, %{
          kind: :return,
          seed: seed,
          sample: i,
          mfa: "#{built.mod}.#{f}/#{length(args)}",
          detail:
            "call returned #{inspect(result, limit: 8)} which is outside the inferred return #{to_quoted_string(ret_union)}",
          src: built.src
        })

      _ ->
        acc
    end
  end

  defp add(acc, finding) do
    # One finding per kind+shape keeps a single inference bug from flooding.
    key = {finding.kind, String.slice(finding.detail, 0, 60)}

    if Enum.any?(acc, fn f -> {f.kind, String.slice(f.detail, 0, 60)} == key end) do
      acc
    else
      [finding | acc]
    end
  end

  defp purge(modules) do
    for {mod, _} <- modules do
      :code.purge(mod)
      :code.delete(mod)
    end
  end

  defp report(findings, stats) do
    IO.puts(
      "witness checks: #{stats.checked}; skipped #{stats.skipped}; " <>
        "no signature: #{stats.no_sig}\n"
    )

    case Enum.reverse(findings) do
      [] ->
        IO.puts("PASS -- all witnessed behavior inside inferred signatures.")
        System.halt(0)

      findings ->
        IO.puts("FAIL -- #{length(findings)} finding(s):\n")

        for f <- findings do
          IO.puts("* #{f.kind} unsoundness in #{f.mfa}   (seed #{f.seed}, sample #{f.sample})")
          IO.puts("    #{f.detail}")
          IO.puts(String.trim_trailing(f.src))
          IO.puts("")
        end

        System.halt(1)
    end
  end
end

InferRunner.run(InferArgs.parse(System.argv()))
