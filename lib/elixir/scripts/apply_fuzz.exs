# Differential false-positive fuzzer for the Elixir type checker
# (Module.Types.{Apply,Expr,Pattern,Of} -- everything above the Descr algebra,
# which descr_fuzz.exs covers).
#
# Why this exists
# ---------------
# Historical false-positive and crash bugs in the checker did not live in
# straight-line arithmetic: they lived in multi-clause pattern subtraction
# ("this clause is redundant" on reachable clauses), binary segments with
# size/unit modifiers, comprehension scoping, protocol/defimpl handling
# (checker crash on `defimpl P, for: <erlang module>`), and guard-driven
# narrowing. So this fuzzer generates programs from a FEATURE GRAMMAR that
# exercises exactly those constructs, always well-typed by construction, each
# with runtime WITNESSES: concrete inputs, one per clause/branch, whose
# expected clause is known at generation time (clause bodies return
# `{tag, value}` so the reached clause is observable).
#
# Oracles
# -------
#   A. EXECUTION FP: the checker emits a type-error warning ("incompatible
#      types given to", "but expected one of:", ...) yet every witness runs
#      clean -- a confirmed false positive.
#   B. CLAUSE REACHABILITY: the checker claims a clause/pattern "will never
#      match" or "is redundant", yet every generated clause is reached by its
#      witness at runtime -- a confirmed false positive.
#   C. CHECKER CRASH: compiling valid generated code raises from Module.Types
#      (or the "please report this bug" internal error) -- a checker bug.
#      (v1 silently ignored ALL compile errors, hiding this whole class.)
#   D. METAMORPHIC: a program that compiles warning-free and runs clean is
#      re-rendered with a semantics-preserving wrapper (case/fn/then around the
#      body); any NEW type warning on the variant (still running clean) is a
#      narrowing/inference asymmetry -- a false positive.
#
# Advisory lints ("will always succeed", "always fail", "evaluates to") are
# excluded on purpose: they legitimately fire on correct-but-redundant code.
#
# How to run
# ----------
#     bin/elixir lib/elixir/scripts/apply_fuzz.exs
#     bin/elixir lib/elixir/scripts/apply_fuzz.exs --seeds 1-20 --samples 500
#
# Deterministic per seed; exits non-zero on any finding. Generator bugs
# (our code failing to compile/run for reasons unrelated to the checker) are
# counted and reported separately -- they should stay at zero.
#
# Validating the oracles (canary runs)
# ------------------------------------
# Because the checker compiles IN-PROCESS, you can validate that the oracles
# still detect bugs by loading a deliberately-broken checker module into the
# running VM before requiring this script -- no rebuild needed:
#
#     Code.put_compiler_option(:ignore_module_conflict, true)
#     # e.g. revert a fixed bug in pattern.ex or narrow a signature in
#     # apply.ex, write to /tmp, then:
#     Code.compile_file("/tmp/pattern_canary.ex")
#     Code.require_file("lib/elixir/scripts/apply_fuzz.exs")
#
# Known-good canaries: reverting the `of_precise_bitstring?` freshness check
# in pattern.ex must trigger the clause-reachability oracle; changing
# byte_size's domain from bitstring() to pid() in apply.ex must trigger the
# execution-FP oracle. Both were verified when this harness was written
# (alongside the live `defimpl ... for: <erlang module>` crash, which the
# crash oracle finds organically).

# ---------------------------------------------------------------------------
# CLI args
# ---------------------------------------------------------------------------

defmodule Args do
  def parse(argv), do: parse(argv, %{seeds: 1..10, samples: 300})

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

# Shared typed-program grammar (Expr/Feature/Build) -- also used by
# infer_soundness.exs.
Code.require_file("apply_grammar.exs", __DIR__)

defmodule Runner do
  @type_error ~r/incompatible types (assigned to|given as|given on|given to|in binary)|incompatible value given to|but expected one of:/
  @clause_error ~r/the following clause (is redundant|will never match)|pattern in clause will never match|the following pattern will never match/
  @crash_marker ~r/checking types|please report this bug/i

  def run(%{seeds: seeds, samples: samples}) do
    IO.puts("apply_fuzz: seeds #{inspect(seeds)}, #{samples} samples/seed\n")
    Code.put_compiler_option(:ignore_module_conflict, true)

    {findings, stats} =
      for seed <- seeds, reduce: {[], %{gen_bugs: 0, compiled: 0}} do
        {acc, stats} ->
          :rand.seed(:exsss, {seed, seed * 7 + 1, seed * 13 + 3})
          run_seed(seed, samples, acc, stats)
      end

    report(findings, stats)
  end

  defp run_seed(seed, samples, acc, stats) do
    Enum.reduce(1..samples, {acc, stats}, fn i, {acc, stats} ->
      features = for j <- 1..:rand.uniform(2), do: Feature.random("#{seed}_#{i}_#{j}")
      built = Build.assemble("ApplyFuzz#{seed}x#{i}", features)

      {acc, stats} = evaluate(built, seed, i, acc, stats)

      # Metamorphic pass on wrappable features when the base was clean.
      Enum.reduce(built.wrappables, {acc, stats}, fn wrappable, {acc, stats} ->
        variant = Build.variant("ApplyFuzzV#{seed}x#{i}", wrappable)
        evaluate(variant, seed, i, acc, stats, _metamorphic = true)
      end)
    end)
  end

  defp evaluate(built, seed, i, acc, stats, metamorphic? \\ false) do
    {result, diagnostics} =
      Code.with_diagnostics(fn ->
        try do
          {:ok, Code.compile_string(built.src)}
        rescue
          e -> {:error, e, __STACKTRACE__}
        end
      end)

    warnings = for d <- diagnostics, d.severity == :warning, do: d.message
    type_warnings = Enum.filter(warnings, &(&1 =~ @type_error))
    clause_warnings = Enum.filter(warnings, &(&1 =~ @clause_error))

    case result do
      {:error, e, stacktrace} ->
        purge_all([])

        if checker_crash?(e, stacktrace) do
          f = finding(:checker_crash, built, seed, i, Exception.message(e), metamorphic?)
          {[f | acc], stats}
        else
          {acc, bump_gen_bug(stats, built, e)}
        end

      {:ok, modules} ->
        stats = %{stats | compiled: stats.compiled + 1}
        exec = execute_witnesses(built)
        purge_all(modules)

        cond do
          exec != :ok ->
            # Our witnesses failed: generator bug (or a genuinely broken
            # program) -- never a checker finding.
            {acc, bump_gen_bug(stats, built, exec)}

          type_warnings != [] ->
            f =
              finding(
                :execution_fp,
                built,
                seed,
                i,
                Enum.join(type_warnings, "\n---\n"),
                metamorphic?
              )

            {[f | acc], stats}

          clause_warnings != [] ->
            # Every generated clause was reached by its witness, so any
            # redundant/never-match claim is refuted by execution.
            f =
              finding(
                :clause_fp,
                built,
                seed,
                i,
                Enum.join(clause_warnings, "\n---\n"),
                metamorphic?
              )

            {[f | acc], stats}

          true ->
            {acc, stats}
        end
    end
  end

  defp checker_crash?(e, stacktrace) do
    Exception.message(e) =~ @crash_marker or
      Enum.any?(stacktrace, fn {mod, _f, _a, _loc} ->
        mod |> Atom.to_string() |> String.starts_with?("Elixir.Module.Types")
      end)
  end

  defp execute_witnesses(built) do
    mod = Module.concat([built.mod])

    Enum.reduce_while(built.witnesses, :ok, fn {f, args, expect}, :ok ->
      try do
        result = apply(mod, f, args)

        case expect do
          {:tag, tag} when elem(result, 0) == tag -> {:cont, :ok}
          {:tag, tag} -> {:halt, {:wrong_clause, f, args, tag, result}}
          :any -> {:cont, :ok}
        end
      rescue
        e -> {:halt, {:witness_raised, f, args, e.__struct__}}
      catch
        kind, v -> {:halt, {:witness_threw, f, args, {kind, v}}}
      end
    end)
  end

  defp purge_all(modules) do
    for {mod, _bin} <- modules do
      :code.purge(mod)
      :code.delete(mod)
    end

    :ok
  end

  defp finding(oracle, built, seed, i, message, metamorphic?) do
    %{
      oracle: oracle,
      seed: seed,
      sample: i,
      src: built.src,
      message: message,
      metamorphic: metamorphic?,
      # Dedup key: oracle + first line of the message with module/atom names
      # normalized away, so one bug hit through different targets (:lists,
      # :queue, ...) or different generated names reports once.
      key:
        {oracle,
         message
         |> String.split("\n")
         |> hd()
         |> String.replace(~r/:[a-z_]+|[A-Z][A-Za-z0-9_.]*|\d+/, "_")
         |> String.slice(0, 80)}
    }
  end

  defp bump_gen_bug(stats, built, why) do
    if System.get_env("APPLY_FUZZ_DEBUG") do
      IO.puts("--- generator bug (#{inspect(why, limit: 5)}):\n#{built.src}\n")
    end

    %{stats | gen_bugs: stats.gen_bugs + 1}
  end

  defp report(findings, stats) do
    findings = findings |> Enum.reverse() |> Enum.uniq_by(& &1.key)

    IO.puts(
      "compiled #{stats.compiled} modules; generator bugs: #{stats.gen_bugs}" <>
        if(stats.gen_bugs > 0, do: "  (set APPLY_FUZZ_DEBUG=1 to inspect)", else: "")
    )

    if findings == [] do
      IO.puts("\nPASS -- no checker findings.")
      System.halt(0)
    else
      IO.puts("\nFAIL -- #{length(findings)} distinct finding(s):\n")

      for f <- findings do
        meta = if f.metamorphic, do: " [metamorphic variant]", else: ""
        IO.puts("### #{f.oracle}#{meta}   (seed #{f.seed}, sample #{f.sample})")
        IO.puts(String.trim_trailing(f.src))

        IO.puts(
          "  >> " <> (f.message |> String.split("\n") |> Enum.take(12) |> Enum.join("\n  >> "))
        )

        IO.puts("")
      end

      System.halt(1)
    end
  end
end

Runner.run(Args.parse(System.argv()))
