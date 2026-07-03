# Recipe representation for Module.Types.Descr types.
#
# A recipe is a build plan for a descr: a tagged tree of constructor calls.
# Keeping the plan (instead of only the opaque descr it builds) buys three
# things:
#
#   1. SHRINKING: when a property fails, structurally simpler recipes can be
#      re-built and re-checked, yielding minimal counterexamples.
#   2. REPORTING: a recipe renders as copy-pasteable `import Module.Types.Descr`
#      constructor source.
#   3. DENOTATION: a finite-universe reference model (descr_model.exs) can
#      compute the exact set of values a recipe denotes, independently of the
#      implementation under test.
#
# Loaded with Code.require_file/1 by descr_model.exs and descr_fuzz.exs.
#
# Grammar (profile :model is the restricted fragment whose denotation the
# finite model can compute exactly; :fuzz is the full fragment):
#
#   r ::= :term | :none
#       | {:base, kind}            kind: :integer :float :binary :bitstring
#                                        :pid :port :reference :empty_list
#                                        (:boolean only in :fuzz)
#       | {:atom, [atom]} | :atom_top
#       | {:union | :inter | :diff, r, r} | {:neg, r}
#       | {:tuple, [r]} | {:open_tuple, [r]} | :tuple_top
#       | {:map, :closed | :open, [{key, :required | :optional, r}]}
#       | :map_top | :empty_map
#       | {:list, r} | {:nel, r} | {:nel, r, r}
#       | :fun_top | {:fun_arity, n}
#       | {:fun, [r], r}           (:fuzz only)
#       | {:dynamic, r} | :dynamic_top   (:fuzz only)
#       | {:domain_map, tag, [{domain_kind, r} | {key, opt, r}]}  (:fuzz only)

defmodule DescrRecipe do
  import Module.Types.Descr

  # ------------------------------------------------------------------------
  # Building: recipe -> descr (via public constructors only)
  # ------------------------------------------------------------------------

  # Raises nothing itself; if a Descr constructor/op crashes, throws
  # {:recipe_crash, op, err} so callers can report a construction bug.
  def build(:term), do: term()
  def build(:none), do: none()
  def build({:base, :integer}), do: integer()
  def build({:base, :float}), do: float()
  def build({:base, :binary}), do: binary()
  def build({:base, :bitstring}), do: bitstring()
  def build({:base, :pid}), do: pid()
  def build({:base, :port}), do: port()
  def build({:base, :reference}), do: reference()
  def build({:base, :empty_list}), do: empty_list()
  def build({:base, :boolean}), do: boolean()
  def build({:atom, atoms}), do: atom(atoms)
  def build(:atom_top), do: atom()
  def build({:union, a, b}), do: op(:opt_union, build(a), build(b))
  def build({:inter, a, b}), do: op(:opt_intersection, build(a), build(b))
  def build({:diff, a, b}), do: op(:opt_difference, build(a), build(b))
  def build({:neg, a}), do: op(:opt_negation, build(a))
  def build({:tuple, elems}), do: tuple(Enum.map(elems, &build/1))
  def build({:open_tuple, elems}), do: open_tuple(Enum.map(elems, &build/1))
  def build(:tuple_top), do: tuple()
  def build(:map_top), do: open_map()
  def build(:empty_map), do: empty_map()

  def build({:map, tag, fields}) do
    built =
      Enum.map(fields, fn {key, optionality, r} ->
        inner = build(r)
        {key, if(optionality == :optional, do: if_set(inner), else: inner)}
      end)

    case tag do
      :closed -> closed_map(built)
      :open -> open_map(built)
    end
  end

  def build({:domain_map, tag, fields}) do
    built =
      Enum.map(fields, fn
        {:domain, kind, r} ->
          {[kind], build(r)}

        {key, optionality, r} ->
          {key, if(optionality == :optional, do: if_set(build(r)), else: build(r))}
      end)

    case tag do
      :closed -> closed_map(built)
      :open -> open_map(built)
    end
  end

  def build({:list, r}), do: list(build(r))
  def build({:nel, r}), do: non_empty_list(build(r))
  def build({:nel, r, l}), do: non_empty_list(build(r), build(l))
  def build(:fun_top), do: fun()
  def build({:fun_arity, n}), do: fun(n)
  def build({:fun, args, ret}), do: fun(Enum.map(args, &build/1), build(ret))
  def build({:dynamic, r}), do: dynamic(build(r))
  def build(:dynamic_top), do: dynamic()

  def build({:fun_strong, r1, r2}) do
    fun_from_non_overlapping_clauses([{[integer()], build(r1)}, {[atom()], build(r2)}])
  end

  def build({:fun_inferred, r1, r2}) do
    fun_from_inferred_clauses([{[integer()], build(r1)}, {[atom()], build(r2)}])
  end

  defp op(name, a), do: safe(name, [a])
  defp op(name, a, b), do: safe(name, [a, b])

  defp safe(name, args) do
    apply(Module.Types.Descr, name, args)
  rescue
    err -> throw({:recipe_crash, name, args, err})
  end

  # ------------------------------------------------------------------------
  # Rendering: recipe -> copy-pasteable constructor source
  # ------------------------------------------------------------------------

  def render(:term), do: "term()"
  def render(:none), do: "none()"
  def render({:base, k}), do: "#{k}()"
  def render({:atom, atoms}), do: "atom(#{inspect(atoms)})"
  def render(:atom_top), do: "atom()"
  def render({:union, a, b}), do: "opt_union(#{render(a)}, #{render(b)})"
  def render({:inter, a, b}), do: "opt_intersection(#{render(a)}, #{render(b)})"
  def render({:diff, a, b}), do: "opt_difference(#{render(a)}, #{render(b)})"
  def render({:neg, a}), do: "opt_negation(#{render(a)})"
  def render({:tuple, es}), do: "tuple([#{Enum.map_join(es, ", ", &render/1)}])"
  def render({:open_tuple, es}), do: "open_tuple([#{Enum.map_join(es, ", ", &render/1)}])"
  def render(:tuple_top), do: "tuple()"
  def render(:map_top), do: "open_map()"
  def render(:empty_map), do: "empty_map()"

  def render({:map, tag, fields}) do
    inner =
      Enum.map_join(fields, ", ", fn {k, o, r} ->
        v = render(r)
        "#{k}: " <> if(o == :optional, do: "if_set(#{v})", else: v)
      end)

    "#{if tag == :closed, do: "closed_map", else: "open_map"}([#{inner}])"
  end

  def render({:domain_map, tag, fields}) do
    inner =
      Enum.map_join(fields, ", ", fn
        {:domain, kind, r} ->
          "{[#{inspect(kind)}], #{render(r)}}"

        {k, o, r} ->
          "{#{inspect(k)}, #{if(o == :optional, do: "if_set(#{render(r)})", else: render(r))}}"
      end)

    "#{if tag == :closed, do: "closed_map", else: "open_map"}([#{inner}])"
  end

  def render({:list, r}), do: "list(#{render(r)})"
  def render({:nel, r}), do: "non_empty_list(#{render(r)})"
  def render({:nel, r, l}), do: "non_empty_list(#{render(r)}, #{render(l)})"
  def render(:fun_top), do: "fun()"
  def render({:fun_arity, n}), do: "fun(#{n})"

  def render({:fun, args, ret}),
    do: "fun([#{Enum.map_join(args, ", ", &render/1)}], #{render(ret)})"

  def render({:dynamic, r}), do: "dynamic(#{render(r)})"
  def render(:dynamic_top), do: "dynamic()"

  def render({:fun_strong, r1, r2}),
    do:
      "fun_from_non_overlapping_clauses([{[integer()], #{render(r1)}}, {[atom()], #{render(r2)}}])"

  def render({:fun_inferred, r1, r2}),
    do: "fun_from_inferred_clauses([{[integer()], #{render(r1)}}, {[atom()], #{render(r2)}}])"

  # ------------------------------------------------------------------------
  # Size (shrinking metric)
  # ------------------------------------------------------------------------

  def size(r) when is_atom(r), do: 1
  def size({:base, _}), do: 1
  def size({:atom, as}), do: 1 + length(as)
  def size({op, a, b}) when op in [:union, :inter, :diff], do: 1 + size(a) + size(b)
  def size({:neg, a}), do: 1 + size(a)
  def size({t, es}) when t in [:tuple, :open_tuple], do: 1 + Enum.sum_by(es, &size/1)
  def size({:map, _, fields}), do: 1 + Enum.sum_by(fields, fn {_, _, r} -> 1 + size(r) end)

  def size({:domain_map, _, fields}),
    do: 1 + Enum.sum_by(fields, fn f -> 1 + size(elem(f, tuple_size(f) - 1)) end)

  def size({:list, r}), do: 1 + size(r)
  def size({:nel, r}), do: 1 + size(r)
  def size({:nel, r, l}), do: 1 + size(r) + size(l)
  def size({:fun_arity, _}), do: 1
  def size({:fun, args, ret}), do: 1 + Enum.sum_by(args, &size/1) + size(ret)
  def size({:dynamic, r}), do: 1 + size(r)
  def size({:fun_strong, r1, r2}), do: 1 + size(r1) + size(r2)
  def size({:fun_inferred, r1, r2}), do: 1 + size(r1) + size(r2)

  # ------------------------------------------------------------------------
  # Shrinking
  # ------------------------------------------------------------------------
  #
  # candidates/1 returns strictly simpler recipes to try. The caller keeps a
  # candidate only if the property still fails on it.

  def candidates(r) do
    (structural(r) ++ recursive(r))
    |> Enum.uniq()
    |> Enum.filter(&(size(&1) < size(r)))
  end

  # Coarse replacements every node admits.
  defp structural(r), do: [:none, :term] -- [r]

  defp recursive({op, a, b}) when op in [:union, :inter, :diff] do
    [a, b] ++
      for(a2 <- candidates(a), do: {op, a2, b}) ++
      for(b2 <- candidates(b), do: {op, a, b2})
  end

  defp recursive({:neg, a}), do: [a] ++ for(a2 <- candidates(a), do: {:neg, a2})

  defp recursive({t, es}) when t in [:tuple, :open_tuple] do
    drops = for i <- 0..(length(es) - 1)//1, do: {t, List.delete_at(es, i)}

    shrunk =
      for {e, i} <- Enum.with_index(es), e2 <- candidates(e) do
        {t, List.replace_at(es, i, e2)}
      end

    drops ++ shrunk ++ [:tuple_top]
  end

  defp recursive({:map, tag, fields}) do
    drops = for i <- 0..(length(fields) - 1)//1, do: {:map, tag, List.delete_at(fields, i)}

    shrunk =
      for {{k, o, fr}, i} <- Enum.with_index(fields), fr2 <- candidates(fr) do
        {:map, tag, List.replace_at(fields, i, {k, o, fr2})}
      end

    required =
      for {{k, :optional, fr}, i} <- Enum.with_index(fields) do
        {:map, tag, List.replace_at(fields, i, {k, :required, fr})}
      end

    drops ++ shrunk ++ required ++ [:map_top, :empty_map]
  end

  defp recursive({:domain_map, tag, fields}) do
    for i <- 0..(length(fields) - 1)//1, do: {:domain_map, tag, List.delete_at(fields, i)}
  end

  defp recursive({:list, r}),
    do: [{:base, :empty_list}, r] ++ for(r2 <- candidates(r), do: {:list, r2})

  defp recursive({:nel, r}), do: for(r2 <- candidates(r), do: {:nel, r2})

  defp recursive({:nel, r, l}) do
    [{:nel, r}] ++
      for(r2 <- candidates(r), do: {:nel, r2, l}) ++
      for(l2 <- candidates(l), do: {:nel, r, l2})
  end

  defp recursive({:atom, atoms}) when length(atoms) > 1 do
    for i <- 0..(length(atoms) - 1)//1, do: {:atom, List.delete_at(atoms, i)}
  end

  defp recursive({:fun, args, ret}) do
    [{:fun_arity, length(args)}, :fun_top] ++
      for(r2 <- candidates(ret), do: {:fun, args, r2}) ++
      for {a, i} <- Enum.with_index(args), a2 <- candidates(a) do
        {:fun, List.replace_at(args, i, a2), ret}
      end
  end

  defp recursive({t, r1, r2}) when t in [:fun_strong, :fun_inferred] do
    [:fun_top, {:fun_arity, 1}] ++
      for(c <- candidates(r1), do: {t, c, r2}) ++
      for(c <- candidates(r2), do: {t, r1, c})
  end

  defp recursive({:dynamic, r}),
    do: [r, :dynamic_top] ++ for(r2 <- candidates(r), do: {:dynamic, r2})

  defp recursive(_), do: []

  # Greedy shrink of a tuple of recipes against a failing property.
  # fail?.(recipes) must return true when the property STILL FAILS.
  # Returns the smallest failing tuple found.
  def shrink(recipes, fail?, budget \\ 2000) do
    do_shrink(Tuple.to_list(recipes), fail?, budget) |> List.to_tuple()
  end

  defp do_shrink(recipes, fail?, budget) when budget > 0 do
    attempt =
      Enum.reduce_while(0..(length(recipes) - 1), nil, fn i, nil ->
        current = Enum.at(recipes, i)

        candidate =
          current
          |> candidates()
          |> Enum.sort_by(&size/1)
          |> Enum.find(fn c ->
            fail?.(List.to_tuple(List.replace_at(recipes, i, c)))
          end)

        case candidate do
          nil -> {:cont, nil}
          c -> {:halt, List.replace_at(recipes, i, c)}
        end
      end)

    case attempt do
      nil -> recipes
      smaller -> do_shrink(smaller, fail?, budget - 1)
    end
  end

  defp do_shrink(recipes, _fail?, _budget), do: recipes

  # ------------------------------------------------------------------------
  # Generators
  # ------------------------------------------------------------------------
  #
  # :model profile — the fragment descr_model.exs can denote exactly:
  #   * recipe atoms drawn from @model_atoms only (the universe holds one
  #     extra fresh atom for complement witnesses)
  #   * constructor elements are FLAT (level-0) recipes: boolean combos of
  #     bases/atom sets, no nested constructors (finite-model adequacy)
  #   * tuple/open_tuple with 0..2 elements; map fields over @model_keys;
  #     nel last types restricted to atom/int/binary/empty_list combos
  #   * no dynamic, no funs beyond fun_top, no domain keys, no boolean()

  @model_atoms [:x, :y]
  @model_keys [:a, :b]
  @flat_bases [:integer, :float, :binary, :bitstring, :pid, :port, :reference, :empty_list]
  @last_bases [:integer, :binary, :empty_list]

  def gen(:model, depth), do: model_recipe(depth)
  def gen(:fuzz, depth), do: fuzz_recipe(depth)

  # Level-0: boolean combinations over bases and atom sets. No constructors.
  def flat(0) do
    case uniform(7) do
      1 -> {:base, Enum.random(@flat_bases)}
      2 -> {:atom, Enum.take_random(@model_atoms, uniform(2))}
      3 -> :atom_top
      4 -> {:base, Enum.random(@flat_bases)}
      5 -> {:atom, [Enum.random(@model_atoms)]}
      6 -> :term
      7 -> :none
    end
  end

  def flat(depth) do
    case uniform(6) do
      1 -> {:union, flat(depth - 1), flat(depth - 1)}
      2 -> {:inter, flat(depth - 1), flat(depth - 1)}
      3 -> {:diff, flat(depth - 1), flat(depth - 1)}
      4 -> {:neg, flat(depth - 1)}
      _ -> flat(0)
    end
  end

  defp last_flat do
    case uniform(4) do
      1 -> {:base, Enum.random(@last_bases)}
      2 -> {:atom, Enum.take_random(@model_atoms, uniform(2))}
      3 -> {:union, {:atom, [Enum.random(@model_atoms)]}, {:base, Enum.random(@last_bases)}}
      4 -> {:base, :empty_list}
    end
  end

  defp model_leaf do
    case uniform(12) do
      1 -> flat(1)
      2 -> {:tuple, flat_list(0..2)}
      3 -> {:open_tuple, flat_list(0..2)}
      4 -> :tuple_top
      5 -> {:map, :closed, model_fields()}
      6 -> {:map, :open, model_fields()}
      7 -> :map_top
      8 -> :empty_map
      9 -> {:list, flat(1)}
      10 -> {:nel, flat(1)}
      11 -> {:nel, flat(1), last_flat()}
      12 -> :fun_top
    end
  end

  defp model_recipe(0), do: model_leaf()

  defp model_recipe(depth) do
    case uniform(6) do
      1 -> {:union, model_recipe(depth - 1), model_recipe(depth - 1)}
      2 -> {:inter, model_recipe(depth - 1), model_recipe(depth - 1)}
      3 -> {:diff, model_recipe(depth - 1), model_recipe(depth - 1)}
      4 -> {:neg, model_recipe(depth - 1)}
      _ -> model_leaf()
    end
  end

  defp flat_list(range) do
    case Enum.random(range) do
      0 -> []
      n -> for _ <- 1..n, do: flat(1)
    end
  end

  defp model_fields do
    @model_keys
    |> Enum.take_random(uniform(2))
    |> Enum.map(fn k ->
      {k, Enum.random([:required, :optional]), flat(1)}
    end)
  end

  # :fuzz profile — full grammar, mirrors descr_fuzz's historical generator.

  @fuzz_atoms [:x, :y, :z]
  @fuzz_keys [:a, :b, :c]
  @fuzz_domains [
    :atom,
    :binary,
    :bitstring_no_binary,
    :float,
    :fun,
    :integer,
    :list,
    :map,
    :pid,
    :port,
    :reference,
    :tuple
  ]

  defp fuzz_base do
    case uniform(18) do
      1 -> {:base, :integer}
      2 -> {:base, :float}
      3 -> {:base, :binary}
      4 -> {:base, :bitstring}
      5 -> {:base, :pid}
      6 -> {:base, :port}
      7 -> {:base, :reference}
      8 -> {:base, :empty_list}
      9 -> {:base, :boolean}
      10 -> {:atom, Enum.take_random(@fuzz_atoms, uniform(3))}
      11 -> {:atom, [Enum.random(@fuzz_atoms)]}
      12 -> :atom_top
      13 -> {:tuple, []}
      14 -> :tuple_top
      15 -> :map_top
      16 -> :term
      17 -> :none
      18 -> {:fun_arity, uniform(3) - 1}
    end
  end

  def fuzz_recipe(0), do: fuzz_base()

  def fuzz_recipe(depth) do
    case uniform(17) do
      n when n in 1..3 -> fuzz_base()
      4 -> {:union, fuzz_recipe(depth - 1), fuzz_recipe(depth - 1)}
      5 -> {:inter, fuzz_recipe(depth - 1), fuzz_recipe(depth - 1)}
      6 -> {:diff, fuzz_recipe(depth - 1), fuzz_recipe(depth - 1)}
      7 -> {:neg, fuzz_recipe(depth - 1)}
      8 -> {:tuple, fuzz_list(depth)}
      9 -> {:open_tuple, fuzz_list(depth)}
      10 -> {:map, :closed, fuzz_fields(depth)}
      11 -> {:map, :open, fuzz_fields(depth)}
      12 -> {:list, fuzz_recipe(depth - 1)}
      13 -> {:nel, fuzz_recipe(depth - 1)}
      14 -> {:nel, fuzz_recipe(depth - 1), fuzz_recipe(depth - 1)}
      15 -> {:fun, [fuzz_recipe(depth - 1)], fuzz_recipe(depth - 1)}
      16 -> {:fun_strong, fuzz_recipe(depth - 1), fuzz_recipe(depth - 1)}
      17 -> maybe_domain_map(depth)
    end
  end

  def fuzz_gradual(0) do
    if uniform(2) == 1, do: {:dynamic, fuzz_base()}, else: fuzz_base()
  end

  def fuzz_gradual(depth) do
    case uniform(16) do
      1 ->
        {:dynamic, fuzz_gradual(depth - 1)}

      2 ->
        :dynamic_top

      n when n in 3..4 ->
        fuzz_base()

      5 ->
        {:union, fuzz_gradual(depth - 1), fuzz_gradual(depth - 1)}

      6 ->
        {:inter, fuzz_gradual(depth - 1), fuzz_gradual(depth - 1)}

      7 ->
        {:diff, fuzz_gradual(depth - 1), fuzz_gradual(depth - 1)}

      8 ->
        {:neg, fuzz_recipe(depth - 1)}

      9 ->
        {:map, :closed, fuzz_gradual_fields(depth)}

      10 ->
        {:map, :open, fuzz_gradual_fields(depth)}

      11 ->
        {:tuple, fuzz_gradual_list(depth)}

      12 ->
        {:open_tuple, fuzz_gradual_list(depth)}

      13 ->
        {:list, fuzz_gradual(depth - 1)}

      14 ->
        {:nel, fuzz_gradual(depth - 1), fuzz_gradual(depth - 1)}

      15 ->
        {:fun, [fuzz_gradual(depth - 1)], fuzz_gradual(depth - 1)}

      16 ->
        {:union, {:dynamic, {:fun_strong, fuzz_recipe(depth - 1), fuzz_recipe(depth - 1)}},
         {:fun_inferred, fuzz_recipe(depth - 1), fuzz_recipe(depth - 1)}}
    end
  end

  defp fuzz_list(depth), do: for(_ <- 1..uniform(3), do: fuzz_recipe(depth - 1))
  defp fuzz_gradual_list(depth), do: for(_ <- 1..uniform(3), do: fuzz_gradual(depth - 1))

  defp fuzz_fields(depth) do
    @fuzz_keys
    |> Enum.shuffle()
    |> Enum.take(uniform(3))
    |> Enum.map(fn k -> {k, Enum.random([:required, :optional]), fuzz_recipe(depth - 1)} end)
  end

  defp fuzz_gradual_fields(depth) do
    @fuzz_keys
    |> Enum.shuffle()
    |> Enum.take(uniform(3))
    |> Enum.map(fn k -> {k, Enum.random([:required, :optional]), fuzz_gradual(depth - 1)} end)
  end

  defp maybe_domain_map(depth) do
    fields =
      [{:domain, Enum.random(@fuzz_domains), fuzz_recipe(depth - 1)}] ++
        Enum.map(Enum.take_random(@fuzz_keys, uniform(2)), fn k ->
          {k, Enum.random([:required, :optional]), fuzz_recipe(depth - 1)}
        end)

    {:domain_map, Enum.random([:closed, :open]), fields}
  end

  # Kind-biased recipes: boolean combinations within one kind over a small
  # alphabet, where projection bugs hide (fully random recipes essentially
  # never produce e.g. difference(open_tuple([]), tuple([]))).

  def biased(:list, depth) when depth <= 0, do: {:list, small(0)}

  def biased(:list, depth) do
    case uniform(8) do
      1 -> {:list, small(depth)}
      2 -> {:nel, small(depth)}
      3 -> {:nel, small(depth), small(depth)}
      4 -> {:union, biased(:list, depth - 1), biased(:list, depth - 1)}
      5 -> {:inter, biased(:list, depth - 1), biased(:list, depth - 1)}
      6 -> {:diff, biased(:list, depth - 1), biased(:list, depth - 1)}
      7 -> {:diff, {:nel, small(depth)}, {:nel, small(depth)}}
      8 -> {:list, small(depth)}
    end
  end

  def biased(:tuple, depth) when depth <= 0, do: :tuple_top

  def biased(:tuple, depth) do
    case uniform(8) do
      1 -> :tuple_top
      2 -> {:tuple, small_list()}
      3 -> {:open_tuple, small_list()}
      4 -> {:union, biased(:tuple, depth - 1), biased(:tuple, depth - 1)}
      5 -> {:inter, biased(:tuple, depth - 1), biased(:tuple, depth - 1)}
      6 -> {:diff, biased(:tuple, depth - 1), biased(:tuple, depth - 1)}
      7 -> {:diff, {:open_tuple, []}, biased(:tuple, depth - 1)}
      8 -> {:tuple, []}
    end
  end

  def biased(:map, depth) when depth <= 0, do: :map_top

  def biased(:map, depth) do
    case uniform(9) do
      1 -> :map_top
      2 -> :empty_map
      3 -> {:map, :closed, small_fields()}
      4 -> {:map, :open, small_fields()}
      5 -> {:union, biased(:map, depth - 1), biased(:map, depth - 1)}
      6 -> {:inter, biased(:map, depth - 1), biased(:map, depth - 1)}
      7 -> {:diff, biased(:map, depth - 1), biased(:map, depth - 1)}
      8 -> {:diff, :map_top, biased(:map, depth - 1)}
      9 -> {:map, :closed, small_fields()}
    end
  end

  # Small element recipes over the fuzz value alphabet, so concrete-value
  # membership flips often.
  def small(depth) when depth <= 0 do
    case uniform(6) do
      1 -> {:atom, [Enum.random(@fuzz_atoms)]}
      2 -> {:atom, Enum.take_random(@fuzz_atoms, uniform(3))}
      3 -> :atom_top
      4 -> {:base, :integer}
      5 -> {:base, :empty_list}
      6 -> :term
    end
  end

  def small(depth) do
    case uniform(9) do
      1 -> {:atom, [Enum.random(@fuzz_atoms)]}
      2 -> {:atom, Enum.take_random(@fuzz_atoms, uniform(3))}
      3 -> :atom_top
      4 -> {:base, :integer}
      5 -> {:union, small(depth - 1), small(depth - 1)}
      6 -> {:diff, small(depth - 1), small(depth - 1)}
      7 -> {:tuple, for(_ <- 1..uniform(2), do: small(depth - 1))}
      8 -> {:map, :closed, [{Enum.random(@fuzz_keys), :required, small(depth - 1)}]}
      9 -> {:nel, small(depth - 1)}
    end
  end

  defp small_list do
    case uniform(3) - 1 do
      0 -> []
      n -> for _ <- 1..n, do: small(1)
    end
  end

  defp small_fields do
    @fuzz_keys
    |> Enum.take_random(uniform(3))
    |> Enum.map(fn k -> {k, Enum.random([:required, :optional]), small(1)} end)
  end

  defp uniform(n), do: :rand.uniform(n)
end
