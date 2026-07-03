# Finite-universe reference model for Module.Types.Descr.
#
# The strongest oracle in this harness family. Types restricted to the :model
# recipe fragment (see descr_recipe.exs) denote sets over a FINITE universe of
# values, so their exact denotation is computable by brute force, independently
# of the implementation under test:
#
#     den(union(a, b))   = den(a) UNION den(b)
#     den(closed_map(f)) = enumerate matching maps
#     subtype?(A, B)     must equal  den(a) SUBSET den(b)
#     empty?(A)          must equal  den(a) == {}
#     ...
#
# Unlike law-based fuzzing (descr_fuzz.exs), this catches implementations that
# are wrong but SELF-CONSISTENT: every relation is compared against enumerated
# ground truth, not against other implementation results.
#
# Universe adequacy
# -----------------
# The universe must contain a witness for every semantically non-empty
# difference the recipe fragment can express, otherwise the model reports
# false failures ("impl says non-empty, my universe has no witness"). This
# drives its shape:
#   * one FRESH atom (:w) recipes cannot name  -> witnesses for atom()-minus-set
#   * one FRESH map key (:zz) recipes cannot name -> witnesses for
#     open-map-minus-closed-key-set
#   * tuples one size LARGER than recipes can mention -> witnesses for
#     "tuple of size >= 3" cells forced by negations
#   * one token per bitmap kind + a fun token -> witnesses for term-minus-kinds
#   * constructor elements are FLAT (level-0) types only, so element witnesses
#     never need nesting beyond what the universe holds
# The costs are documented per decision below; the trade is that NESTED
# constructor interactions (tuple-of-tuple types etc.) are out of scope here
# and remain covered by descr_fuzz's sampled value model.
#
# Layers
# ------
#   A. Relations: empty?/subtype?/equal?/disjoint? against exact set relations,
#      plus freshly composed union/inter/diff/neg nodes.
#   B. Membership: the implementation's membership decision (singleton subtype?
#      for non-list values, :list-BDD evaluation for list values) against exact
#      den membership -- this independently validates descr_fuzz's value model.
#   C. Projections with EXACT preconditions derived from den: tuple_fetch may
#      return :badindex only if some member truly lacks the index (decidable
#      here, unlike in descr_fuzz); list_hd/list_tl/map_fetch_key likewise;
#      plus membership of concrete projection outcomes in result descrs.
#
# On failure the recipe pair is SHRUNK (descr_recipe.exs) and reported as
# copy-pasteable constructor source.
#
# How to run
# ----------
#     bin/elixir lib/elixir/scripts/descr_model.exs
#     bin/elixir lib/elixir/scripts/descr_model.exs --seeds 1-10 --samples 500 --depth 3
#
# Deterministic per seed; exits non-zero on any violation.
#
# Validating the oracle (canary runs)
# -----------------------------------
# Load a deliberately-broken Module.Types.Descr into the VM, then run the
# model in-process. IMPORTANT: compile this script's modules BEFORE loading
# the broken Descr (the compiler's own checker uses Descr while compiling),
# and choose patches that keep descr SHAPES valid or the checker crashes on
# the patched module itself. Two verified canaries:
#   * blatant: make :atom intersection compute union -> caught within ~30
#     samples by "composed ops match den".
#   * wrong-but-consistent: make integer/0 return the float bitmap. Law-based
#     fuzzing (descr_fuzz.exs) CANNOT see this: every use is poisoned
#     consistently, including sampled-value singletons. This model catches it
#     ("empty? matches den" on the shrunken intersection(integer(), float()),
#     membership mismatches, subtype disagreements) within a few hundred
#     samples -- the reason this tool exists.

Code.require_file("descr_recipe.exs", __DIR__)

import Module.Types.Descr

defmodule Args do
  def parse(argv), do: parse(argv, %{seeds: 1..5, samples: 300, depth: 3})

  defp parse([], acc), do: acc
  defp parse(["--seeds", v | rest], acc), do: parse(rest, %{acc | seeds: range(v)})

  defp parse(["--samples", v | rest], acc),
    do: parse(rest, %{acc | samples: String.to_integer(v)})

  defp parse(["--depth", v | rest], acc), do: parse(rest, %{acc | depth: String.to_integer(v)})
  defp parse([other | _], _), do: raise("unknown arg: #{other}")

  defp range(v) do
    case String.split(v, "-") do
      [a, b] -> String.to_integer(a)..String.to_integer(b)
      [a] -> String.to_integer(a)..String.to_integer(a)
    end
  end
end

# ---------------------------------------------------------------------------
# The universe
# ---------------------------------------------------------------------------
#
# Values:
#   atoms :x, :y (usable in recipes) and :w (fresh)
#   kind tokens {:t, kind} for integer/float/binary/bits/pid/port/reference/fun
#   [] (empty list)
#   tuples of element values: sizes 0..2 fully, size 3 with fixed third element
#   maps over keys :a, :b (recipes) and :zz (fresh, fixed value)
#   lists: proper length 1..2; improper length 1..2 with terminator drawn from
#     every value the :model fragment can name in last position (atoms + int +
#     binary) plus the fresh atom

defmodule Universe do
  @atoms [:x, :y, :w]
  @kinds [:integer, :float, :binary, :bits, :pid, :port, :reference, :fun]
  @filler {:t, :integer}

  def elements do
    @atoms ++ Enum.map(@kinds, &{:t, &1}) ++ [[]]
  end

  def tuples do
    e = elements()

    [{}] ++
      for(v <- e, do: {v}) ++
      for(v <- e, w <- e, do: {v, w}) ++
      for(v <- e, w <- e, do: {v, w, @filler})
  end

  def maps do
    e = elements()

    base =
      [%{}] ++
        for(v <- e, do: %{a: v}) ++
        for(v <- e, do: %{b: v}) ++
        for(v <- e, w <- e, do: %{a: v, b: w})

    base ++ Enum.map(base, &Map.put(&1, :zz, @filler))
  end

  # Lists are stored decomposed as {:l, elements, terminator} to avoid
  # confusing improper cons cells with our token tuples; terminator [] means
  # proper. Rendered back to real lists only when calling real projections.
  @terminators [:x, :y, :w, {:t, :integer}, {:t, :binary}]

  def lists do
    e = elements()

    proper =
      for(v <- e, do: {:l, [v], []}) ++
        for(v <- e, w <- e, do: {:l, [v, w], []})

    improper =
      for t <- @terminators, v <- e, do: {:l, [v], t}

    improper2 =
      for t <- @terminators, v <- e, w <- e, do: {:l, [v, w], t}

    proper ++ improper ++ improper2
  end

  def all do
    elements() ++ tuples() ++ maps() ++ lists()
  end

  def atoms, do: @atoms
end

# ---------------------------------------------------------------------------
# Denotation: :model recipe -> MapSet of universe values
# ---------------------------------------------------------------------------

defmodule Den do
  # Classes are recorded BY CONSTRUCTION: universe values include terms like
  # {:t, kind} tokens and {:l, elems, term} decomposed lists which would fool
  # any is_tuple/is_map shape guessing.
  def new do
    all = Universe.all()

    %{
      all: MapSet.new(all),
      atoms: MapSet.new(Universe.atoms()),
      tuples: Universe.tuples(),
      maps: Universe.maps(),
      lists: Universe.lists()
    }
  end

  def den(u, :term), do: u.all
  def den(_u, :none), do: MapSet.new()
  def den(_u, {:base, :integer}), do: MapSet.new([{:t, :integer}])
  def den(_u, {:base, :float}), do: MapSet.new([{:t, :float}])
  def den(_u, {:base, :binary}), do: MapSet.new([{:t, :binary}])
  def den(_u, {:base, :bitstring}), do: MapSet.new([{:t, :binary}, {:t, :bits}])
  def den(_u, {:base, :pid}), do: MapSet.new([{:t, :pid}])
  def den(_u, {:base, :port}), do: MapSet.new([{:t, :port}])
  def den(_u, {:base, :reference}), do: MapSet.new([{:t, :reference}])
  def den(_u, {:base, :empty_list}), do: MapSet.new([[]])
  def den(_u, {:atom, atoms}), do: MapSet.new(atoms)
  def den(u, :atom_top), do: u.atoms
  def den(u, {:union, a, b}), do: MapSet.union(den(u, a), den(u, b))
  def den(u, {:inter, a, b}), do: MapSet.intersection(den(u, a), den(u, b))
  def den(u, {:diff, a, b}), do: MapSet.difference(den(u, a), den(u, b))
  def den(u, {:neg, a}), do: MapSet.difference(u.all, den(u, a))
  def den(_u, :fun_top), do: MapSet.new([{:t, :fun}])
  def den(u, :tuple_top), do: MapSet.new(u.tuples)
  def den(u, :map_top), do: MapSet.new(u.maps)
  def den(_u, :empty_map), do: MapSet.new([%{}])

  def den(u, {:tuple, elems}) do
    n = length(elems)
    dens = Enum.map(elems, &den(u, &1))

    u.tuples
    |> Enum.filter(fn t ->
      tuple_size(t) == n and elems_match?(Tuple.to_list(t), dens)
    end)
    |> MapSet.new()
  end

  def den(u, {:open_tuple, elems}) do
    n = length(elems)
    dens = Enum.map(elems, &den(u, &1))

    u.tuples
    |> Enum.filter(fn t ->
      tuple_size(t) >= n and elems_match?(Enum.take(Tuple.to_list(t), n), dens)
    end)
    |> MapSet.new()
  end

  def den(u, {:map, tag, fields}) do
    dens = Map.new(fields, fn {k, o, r} -> {k, {o, den(u, r)}} end)
    field_keys = Map.keys(dens)

    u.maps
    |> Enum.filter(fn m ->
      required_ok? =
        Enum.all?(dens, fn {k, {o, d}} ->
          case m do
            %{^k => v} -> MapSet.member?(d, v)
            %{} -> o == :optional
          end
        end)

      closed_ok? = tag == :open or Enum.all?(Map.keys(m), &(&1 in field_keys))
      required_ok? and closed_ok?
    end)
    |> MapSet.new()
  end

  def den(u, {:list, e}), do: MapSet.put(den(u, {:nel, e}), [])

  def den(u, {:nel, e}), do: den(u, {:nel, e, {:base, :empty_list}})

  def den(u, {:nel, e, l}) do
    ed = den(u, e)
    ld = den(u, l)

    u.lists
    |> Enum.filter(fn {:l, elems, terminator} ->
      Enum.all?(elems, &MapSet.member?(ed, &1)) and MapSet.member?(ld, terminator)
    end)
    |> MapSet.new()
  end

  defp elems_match?(values, dens) do
    Enum.zip(values, dens)
    |> Enum.all?(fn {v, d} -> MapSet.member?(d, v) end)
  end
end

# ---------------------------------------------------------------------------
# Implementation-side membership (Layer B subject)
# ---------------------------------------------------------------------------
#
# Decides `value in descr` using the implementation under test:
#   - non-list values: subtype?(single(value), descr)
#   - list values: evaluate the :list BDD (node {_,lit,c,u,d} =
#     (lit and c) or u or (not lit and d); literal {_, elem, last} holds when
#     all elements and the terminator belong).
# Throws {:model_skip, reason} on unknown internals.

defmodule Member do
  import Module.Types.Descr

  def member?(v, t) do
    cond do
      t == :term -> true
      not is_map(t) -> throw({:model_skip, "non-map descr"})
      is_map_key(t, :dynamic) -> throw({:model_skip, "gradual descr"})
      match?({:l, _, _}, v) -> list_member?(v, t)
      true -> subtype?(single(v), t)
    end
  end

  defp list_member?({:l, elems, terminator}, t) do
    case t do
      %{list: bdd} -> eval_bdd(bdd, elems, terminator)
      %{} -> false
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

  defp eval_bdd(other, _e, _t), do: throw({:model_skip, "unknown BDD node: #{inspect(other)}"})

  defp literal(elem, last, elems, terminator) do
    Enum.all?(elems, &member?(&1, elem)) and member?(terminator, last)
  end

  def single(v) when is_atom(v) and not is_boolean(v) and v != nil, do: atom([v])
  def single({:t, :integer}), do: integer()
  def single({:t, :float}), do: float()
  def single({:t, :binary}), do: binary()
  def single({:t, :bits}), do: opt_difference(bitstring(), binary())
  def single({:t, :pid}), do: pid()
  def single({:t, :port}), do: port()
  def single({:t, :reference}), do: reference()
  def single({:t, :fun}), do: fun()
  def single([]), do: empty_list()
  def single(v) when is_tuple(v), do: tuple(Enum.map(Tuple.to_list(v), &single/1))
  def single(v) when is_map(v), do: closed_map(Enum.map(v, fn {k, w} -> {k, single(w)} end))

  # Rendering universe values for reports.
  def render({:t, kind}), do: "<#{kind}>"
  def render({:l, elems, []}), do: "[" <> Enum.map_join(elems, ", ", &render/1) <> "]"

  def render({:l, elems, t}),
    do: "[" <> Enum.map_join(elems, ", ", &render/1) <> " | " <> render(t) <> "]"

  def render(v) when is_tuple(v),
    do: "{" <> Enum.map_join(Tuple.to_list(v), ", ", &render/1) <> "}"

  def render(v) when is_map(v),
    do: "%{" <> Enum.map_join(v, ", ", fn {k, w} -> "#{k}: #{render(w)}" end) <> "}"

  def render(v), do: inspect(v)
end

# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------

defmodule Checks do
  import Module.Types.Descr

  # Each check: {name, fn(universe, r1, r2) -> :ok | {:violation, details}}.
  # Recipes are rebuilt inside so the same functions drive shrinking.

  def all do
    [
      {"empty? matches den", &empty_check/3},
      {"subtype? matches den subset", &subtype_check/3},
      {"equal? matches den equality", &equal_check/3},
      {"disjoint? matches den disjointness", &disjoint_check/3},
      {"composed ops match den", &compose_check/3},
      {"membership matches den", &membership_check/3},
      {"list projections sound+exact verdicts", &list_projection_check/3},
      {"tuple projections sound+exact verdicts", &tuple_projection_check/3},
      {"map projections sound+exact verdicts", &map_projection_check/3}
    ]
  end

  defp build!(r), do: DescrRecipe.build(r)

  defp empty_check(u, r1, _r2) do
    d = build!(r1)
    set = Den.den(u, r1)

    if empty?(d) == (MapSet.size(set) == 0) do
      :ok
    else
      {:violation,
       "empty?/1 says #{empty?(d)} but den has #{MapSet.size(set)} member(s)" <>
         witness(set)}
    end
  end

  defp subtype_check(u, r1, r2) do
    d1 = build!(r1)
    d2 = build!(r2)
    s1 = Den.den(u, r1)
    s2 = Den.den(u, r2)

    cond do
      subtype?(d1, d2) != MapSet.subset?(s1, s2) ->
        {:violation,
         "subtype?(a, b) says #{subtype?(d1, d2)}, den says #{MapSet.subset?(s1, s2)}" <>
           witness(MapSet.difference(s1, s2))}

      subtype?(d2, d1) != MapSet.subset?(s2, s1) ->
        {:violation,
         "subtype?(b, a) says #{subtype?(d2, d1)}, den says #{MapSet.subset?(s2, s1)}" <>
           witness(MapSet.difference(s2, s1))}

      true ->
        :ok
    end
  end

  defp equal_check(u, r1, r2) do
    d1 = build!(r1)
    d2 = build!(r2)
    same = MapSet.equal?(Den.den(u, r1), Den.den(u, r2))

    if equal?(d1, d2) == same do
      :ok
    else
      {:violation, "equal? says #{equal?(d1, d2)}, den says #{same}"}
    end
  end

  defp disjoint_check(u, r1, r2) do
    d1 = build!(r1)
    d2 = build!(r2)
    inter = MapSet.intersection(Den.den(u, r1), Den.den(u, r2))

    if disjoint?(d1, d2) == (MapSet.size(inter) == 0) do
      :ok
    else
      {:violation,
       "disjoint? says #{disjoint?(d1, d2)}, den intersection has #{MapSet.size(inter)}" <>
         witness(inter)}
    end
  end

  # Compose fresh op nodes on top and validate them against den too.
  defp compose_check(u, r1, r2) do
    Enum.reduce_while([:union, :inter, :diff], :ok, fn op, :ok ->
      r3 = {op, r1, r2}
      d3 = build!(r3)
      s3 = Den.den(u, r3)

      cond do
        empty?(d3) != (MapSet.size(s3) == 0) ->
          {:halt,
           {:violation, "#{op}: empty? says #{empty?(d3)}, den says #{MapSet.size(s3) == 0}"}}

        subtype?(d3, build!(r1)) != MapSet.subset?(s3, Den.den(u, r1)) ->
          {:halt, {:violation, "#{op}: subtype vs first operand disagrees with den"}}

        true ->
          {:cont, :ok}
      end
    end)
  end

  defp membership_check(u, r1, _r2) do
    d1 = build!(r1)
    s1 = Den.den(u, r1)

    ins = Enum.take(s1, 6)
    outs = u.all |> MapSet.difference(s1) |> Enum.take(6)

    Enum.reduce_while(ins ++ outs, :ok, fn v, :ok ->
      expected = MapSet.member?(s1, v)

      if Member.member?(v, d1) == expected do
        {:cont, :ok}
      else
        {:halt,
         {:violation,
          "member #{Member.render(v)}: impl says #{not expected}, den says #{expected}"}}
      end
    end)
  end

  defp list_projection_check(u, r1, _r2) do
    d1 = build!(r1)
    s1 = Den.den(u, r1)
    members = Enum.filter(s1, &match?({:l, _, _}, &1))

    # Exact verdict: list_hd/list_tl must succeed iff every member is a
    # non-empty list (den decides exactly).
    only_lists? = MapSet.size(s1) > 0 and MapSet.size(s1) == length(members)

    check_hd =
      case {list_hd(d1), only_lists?} do
        {{:ok, _}, _} -> :ok
        {_err, true} -> {:violation, "list_hd errored but every member is a non-empty list"}
        {_err, false} -> :ok
      end

    with :ok <- check_hd do
      Enum.reduce_while(Enum.take(members, 5), :ok, fn {:l, [h | rest], terminator}, :ok ->
        hd_ok =
          case list_hd(d1) do
            {:ok, ht} -> Member.member?(h, ht)
            _ -> true
          end

        tl_ok =
          case list_tl(d1) do
            {:ok, tt} ->
              tail =
                case {rest, terminator} do
                  {[], []} -> []
                  {[], t} -> t
                  {rest, t} -> {:l, rest, t}
                end

              Member.member?(tail, tt)

            _ ->
              true
          end

        cond do
          not hd_ok ->
            {:halt, {:violation, "head #{Member.render(h)} not in list_hd result"}}

          not tl_ok ->
            {:halt,
             {:violation,
              "tail of #{Member.render({:l, [h | rest], terminator})} not in list_tl result"}}

          true ->
            {:cont, :ok}
        end
      end)
    end
  end

  # A universe value is a tuple VALUE only if it is not one of our tagged
  # representations (kind tokens {:t, k}, decomposed lists {:l, es, t}).
  defp tuple_value?(v),
    do: is_tuple(v) and not match?({:t, _}, v) and not match?({:l, _, _}, v)

  defp tuple_projection_check(u, r1, _r2) do
    d1 = build!(r1)
    s1 = Den.den(u, r1)
    members = Enum.filter(s1, &tuple_value?/1)
    only_tuples? = MapSet.size(s1) > 0 and MapSet.size(s1) == length(members)

    Enum.reduce_while(0..2, :ok, fn i, :ok ->
      # Exact precondition from den: every member has index i?
      all_have? = only_tuples? and Enum.all?(members, &(tuple_size(&1) > i))
      with_index = Enum.filter(members, &(tuple_size(&1) > i))

      case tuple_fetch(d1, i) do
        {_opt, t} ->
          bad =
            with_index
            |> Enum.take(4)
            |> Enum.find(fn v -> not Member.member?(elem(v, i), t) end)

          if bad do
            {:halt,
             {:violation, "elem(#{Member.render(bad)}, #{i}) not in tuple_fetch(_, #{i}) result"}}
          else
            {:cont, :ok}
          end

        :badindex when all_have? ->
          {:halt,
           {:violation,
            ":badindex at #{i} but every member tuple has that index (den-exact false positive)"}}

        :badtuple when only_tuples? ->
          {:halt, {:violation, ":badtuple but every member is a tuple"}}

        _ ->
          {:cont, :ok}
      end
    end)
  end

  defp map_projection_check(u, r1, _r2) do
    d1 = build!(r1)
    s1 = Den.den(u, r1)
    members = Enum.filter(s1, &is_map/1)
    only_maps? = MapSet.size(s1) > 0 and MapSet.size(s1) == length(members)

    Enum.reduce_while([:a, :b], :ok, fn k, :ok ->
      all_have? = only_maps? and Enum.all?(members, &is_map_key(&1, k))
      with_key = Enum.filter(members, &is_map_key(&1, k))

      case map_fetch_key(d1, k) do
        {_opt, t} ->
          bad =
            with_key
            |> Enum.take(4)
            |> Enum.find(fn m -> not Member.member?(Map.fetch!(m, k), t) end)

          if bad do
            {:halt, {:violation, "#{Member.render(bad)}.#{k} not in map_fetch_key result"}}
          else
            {:cont, :ok}
          end

        :badkey when all_have? ->
          {:halt,
           {:violation,
            ":badkey for #{k} but every member map has the key (den-exact false positive)"}}

        :badmap when only_maps? ->
          {:halt, {:violation, ":badmap but every member is a map"}}

        _ ->
          {:cont, :ok}
      end
    end)
  end

  defp witness(set) do
    case Enum.take(set, 3) do
      [] -> ""
      vs -> "; witnesses: " <> Enum.map_join(vs, ", ", &Member.render/1)
    end
  end
end

# ---------------------------------------------------------------------------
# Runner with shrinking
# ---------------------------------------------------------------------------

defmodule Runner do
  def run(%{seeds: seeds, samples: samples, depth: depth}) do
    u = Den.new()

    IO.puts(
      "descr_model: universe of #{MapSet.size(u.all)} values; " <>
        "seeds #{inspect(seeds)}, #{samples} samples/seed, depth #{depth}\n"
    )

    {failures, skips} =
      for seed <- seeds, reduce: {[], 0} do
        {acc, skips} ->
          :rand.seed(:exsss, {seed, seed * 7 + 1, seed * 13 + 3})
          run_seed(u, seed, samples, depth, acc, skips)
      end

    report(failures, skips)
  end

  defp run_seed(u, seed, samples, depth, acc, skips) do
    Enum.reduce(1..samples, {acc, skips}, fn i, {acc, skips} ->
      r1 = DescrRecipe.gen(:model, depth)
      r2 = DescrRecipe.gen(:model, depth)

      Enum.reduce(Checks.all(), {acc, skips}, fn {name, check}, {acc, skips} ->
        case eval_check(u, check, r1, r2) do
          :ok ->
            {acc, skips}

          :model_skip ->
            {acc, skips + 1}

          {:violation, details} ->
            if Enum.any?(acc, &(&1.check == name)) do
              {acc, skips}
            else
              {small1, small2} = shrink(u, check, r1, r2)
              {:violation, small_details} = eval_check(u, check, small1, small2)

              finding = %{
                check: name,
                seed: seed,
                sample: i,
                r1: small1,
                r2: small2,
                details: small_details,
                original_details: details
              }

              {[finding | acc], skips}
            end
        end
      end)
    end)
  end

  defp eval_check(u, check, r1, r2) do
    try do
      check.(u, r1, r2)
    catch
      {:model_skip, _reason} ->
        :model_skip

      {:recipe_crash, op, _args, err} ->
        {:violation, "constructor #{op} crashed: #{Exception.message(err)}"}
    end
  end

  defp shrink(u, check, r1, r2) do
    fail? = fn {c1, c2} ->
      match?({:violation, _}, eval_check(u, check, c1, c2))
    end

    DescrRecipe.shrink({r1, r2}, fail?)
  end

  defp report(failures, skips) do
    if skips > 0, do: IO.puts("note: #{skips} checks skipped (membership model did not apply)\n")

    case Enum.reverse(failures) do
      [] ->
        IO.puts("PASS -- implementation matches the finite model.")
        System.halt(0)

      failures ->
        IO.puts("FAIL -- #{length(failures)} distinct check(s) violated:\n")

        for f <- failures do
          IO.puts("* #{f.check}   (seed #{f.seed}, sample #{f.sample})")
          IO.puts("    #{f.details}")
          IO.puts("    a = #{DescrRecipe.render(f.r1)}")
          IO.puts("    b = #{DescrRecipe.render(f.r2)}")
          IO.puts("")
        end

        System.halt(1)
    end
  end
end

Runner.run(Args.parse(System.argv()))
