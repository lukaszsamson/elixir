# Property-based fuzzer for the set-theoretic type algebra in
# Module.Types.Descr.
#
# Why this exists
# ---------------
# The checker decides "does this code warn?" by computing subtype?/empty? over
# types built with union/intersection/difference/negation, and by projecting
# through operations (list_hd/list_tl, tuple_fetch/insert/delete, map_fetch_key/
# map_put, fun_apply). A wrong answer in either layer produces FALSE POSITIVES
# (warnings on correct code) or checker crashes. Bugs found by this harness
# family include unsound map/tuple difference fast paths, list_tl dropping
# reachable tails, tuple_fetch returning :badindex for always-valid accesses,
# map_put excluding achievable results, and crashes in to_quoted_string.
#
# Oracles, strongest first
# ------------------------
# 1. VALUE MODEL (ground truth). We generate concrete VALUES alongside types
#    and decide membership `v ∈ t` independently of most of the algebra:
#      - atoms, kind tokens (integer/float/binary/pid/...), [] and tuples/maps
#        thereof are "singleton-expressible": membership is subtype?(single(v), t)
#        where single(v) is built from public constructors. (Kind tokens are
#        exact because descr granularity cannot split a bitmap kind.)
#      - proper/improper LIST values are not singleton-expressible, so we
#        evaluate the descr's :list BDD directly: a literal {_, elem, last}
#        contains a non-empty list iff every element ∈ elem and the terminator
#        (the final non-cons tail, [] for proper lists) ∈ last; a node
#        {_, lit, c, u, d} means (lit ∧ c) ∨ u ∨ (¬lit ∧ d). This is the only
#        place we read descr internals; unknown shapes are counted as skips
#        rather than failures so the harness degrades loudly-but-gracefully
#        across refactors.
#    Membership must then commute with every boolean op, agree with subtype?/
#    empty?, and be preserved by every PROJECTION: if v ∈ t and v = [h | rest],
#    then h ∈ list_hd(t) and rest ∈ list_tl(t); if v is a tuple, elem(v, i) ∈
#    tuple_fetch(t, i) and inserted/deleted variants belong to
#    tuple_insert_at/tuple_delete_at results; if v is a map, Map.put(v, k, w) ∈
#    map_put(t, ...) results. This is what catches projection bugs that pure
#    subtype?/empty? laws cannot see.
# 2. CONGRUENCE. Rebuild a' with equal?(a, a') via double negation and the
#    partition identity; every operation must give equal? results and the same
#    verdict shape on a and a'. Catches representation-sensitive fast paths.
# 3. BOOLEAN/LATTICE laws on the static fragment, singleton membership laws,
#    gradual interval laws (re-derivations of Descr's own decomposition, see
#    the note below), and totality (no public op or the printer may crash).
#
# Verdict-coverage oracles: tuple_fetch may return :badindex only if some
# member tuple lacks the index — if t ⊆ open_tuple(i+1 elements) and t is
# non-empty, :badindex is a confirmed false positive. Same for map_fetch_key's
# :badkey vs t ⊆ open_map with the key required.
#
# Gradual laws are NOT an independent specification: they re-derive how Descr
# decomposes gradual types into [lower_bound, upper_bound] intervals
# (Definition 6.5 of V. Lanvin's thesis, https://vlanvin.fr/papers/thesis.pdf,
# cited by subtype?/2). They validate internal consistency of fast paths and
# catch crashes; the value model is the independent ground truth and runs on
# the static fragment.
#
# How to run
# ----------
#     bin/elixir lib/elixir/scripts/descr_fuzz.exs
#     bin/elixir lib/elixir/scripts/descr_fuzz.exs --seeds 1-50 --samples 2000 --depth 4
#
# Deterministic per seed. Descr operands are generated as RECIPES
# (descr_recipe.exs) and greedily SHRUNK on failure -- reports show minimal
# counterexamples as copy-pasteable constructor source (the shrinker converges
# to e.g. `opt_difference(open_tuple([]), tuple([]))` for the tuple_fetch
# soundness bug). Laws that draw randomness internally are re-evaluated under a
# snapshotted PRNG state during shrinking, so shrinks are exact. Exits non-zero
# on any failure, so it can gate CI. Set DESCR_FUZZ_RAW=1 for raw descr dumps.

Code.require_file("descr_recipe.exs", __DIR__)

import Module.Types.Descr

# ---------------------------------------------------------------------------
# CLI args
# ---------------------------------------------------------------------------

defmodule Args do
  def parse(argv) do
    parse(argv, %{seeds: 1..10, samples: 500, depth: 4})
  end

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
# Concrete values and their singleton types
# ---------------------------------------------------------------------------
#
# Values are plain Elixir terms built from:
#   - atoms :x, :y, :z
#   - kind tokens {:token, kind} standing for "an arbitrary value of that
#     bitmap kind" (integer/float/binary/bitstring-not-binary/pid/port/ref).
#     Exact at descr granularity: no descr distinguishes two integers.
#   - [] (empty list)
#   - tuples and atom-keyed maps of the above (no list children, so that
#     membership stays decidable via singleton types)
#   - proper and improper lists of any of the above (incl. nested lists)

defmodule Val do
  import Module.Types.Descr

  @atoms [:x, :y, :z]
  @keys [:a, :b, :c]
  @tokens [:integer, :float, :binary, :bits, :pid, :port, :reference]

  def value(depth) do
    case :rand.uniform(if depth > 0, do: 10, else: 6) do
      1 -> Enum.random(@atoms)
      2 -> {:token, Enum.random(@tokens)}
      3 -> []
      4 -> Enum.random(@atoms)
      5 -> {:token, Enum.random(@tokens)}
      6 -> Enum.random(@atoms)
      7 -> List.to_tuple(for _ <- 1..:rand.uniform(3), do: flat(depth - 1))
      8 -> Map.new(Enum.take(Enum.shuffle(@keys), :rand.uniform(2)), &{&1, flat(depth - 1)})
      9 -> list_value(depth - 1)
      10 -> list_value(depth - 1)
    end
  end

  # A value guaranteed to contain no list at any depth (so tuples/maps of them
  # remain singleton-expressible).
  def flat(depth) do
    case :rand.uniform(if depth > 0, do: 5, else: 3) do
      1 -> Enum.random(@atoms)
      2 -> {:token, Enum.random(@tokens)}
      3 -> Enum.random(@atoms)
      4 -> List.to_tuple(for _ <- 1..:rand.uniform(2), do: flat(depth - 1))
      5 -> Map.new([{Enum.random(@keys), flat(depth - 1)}])
    end
  end

  def list_value(depth) do
    elems = for _ <- 1..:rand.uniform(3), do: value(max(depth, 0))

    case :rand.uniform(4) do
      # improper list: terminator is a non-list, non-[] flat value
      1 -> improper(elems, non_list_terminator(depth))
      _ -> elems
    end
  end

  # Pure-atom lists over the tiny alphabet: the highest-yield witnesses for
  # list projection bugs (their tails flip membership in atom-set list types).
  def atom_list do
    elems = for _ <- 1..:rand.uniform(3), do: Enum.random(@atoms)

    case :rand.uniform(4) do
      1 -> improper(elems, Enum.random(@atoms))
      _ -> elems
    end
  end

  # Value generator biased for the projection oracles.
  def projection_value(depth) do
    if :rand.uniform(3) == 1, do: atom_list(), else: value(depth)
  end

  defp non_list_terminator(depth) do
    case flat(max(depth, 0)) do
      [] -> Enum.random(@atoms)
      other -> other
    end
  end

  defp improper([e], t), do: [e | t]
  defp improper([e | rest], t), do: [e | improper(rest, t)]

  # Is this value a cons cell (non-empty list, proper or improper)?
  def cons?([_ | _]), do: true
  def cons?(_), do: false

  # Decompose a cons into {elements, terminator}. Terminator is [] for proper.
  def decompose([h | t]) when is_list(t) and t != [], do: prepend(h, decompose(t))
  def decompose([h | t]) when t == [], do: {[h], []}
  def decompose([h | t]), do: {[h], t}

  defp prepend(h, {elems, term}), do: {[h | elems], term}

  # The singleton descr of a non-cons value (exact at descr granularity).
  def single(v) when is_atom(v) and v not in [[]], do: atom([v])
  def single({:token, :integer}), do: integer()
  def single({:token, :float}), do: float()
  def single({:token, :binary}), do: binary()
  def single({:token, :bits}), do: opt_difference(bitstring(), binary())
  def single({:token, :pid}), do: pid()
  def single({:token, :port}), do: port()
  def single({:token, :reference}), do: reference()
  def single([]), do: empty_list()
  def single(v) when is_tuple(v), do: tuple(Enum.map(Tuple.to_list(v), &single/1))
  def single(v) when is_map(v), do: closed_map(Enum.map(v, fn {k, w} -> {k, single(w)} end))

  # Runtime-ish rendering for failure reports.
  def render({:token, kind}), do: "<#{kind}>"

  def render(v) when is_tuple(v),
    do: "{" <> Enum.map_join(Tuple.to_list(v), ", ", &render/1) <> "}"

  def render(v) when is_map(v),
    do: "%{" <> Enum.map_join(v, ", ", fn {k, w} -> "#{k}: #{render(w)}" end) <> "}"

  def render(v) when is_list(v) do
    case decompose_safe(v) do
      {elems, []} -> "[" <> Enum.map_join(elems, ", ", &render/1) <> "]"
      {elems, t} -> "[" <> Enum.map_join(elems, ", ", &render/1) <> " | " <> render(t) <> "]"
    end
  end

  def render(v), do: inspect(v)

  defp decompose_safe([]), do: {[], []}
  defp decompose_safe(v), do: decompose(v)
end

# ---------------------------------------------------------------------------
# The value model: ground-truth membership
# ---------------------------------------------------------------------------

defmodule Model do
  import Module.Types.Descr

  # member?(value, static_descr) -> boolean
  # Throws {:model_skip, reason} when the descr uses shapes the model does not
  # understand (counted, not failed).
  def member?(v, t) do
    cond do
      t == :term ->
        true

      not is_map(t) ->
        throw({:model_skip, "non-map descr: #{inspect(t)}"})

      is_map_key(t, :dynamic) ->
        throw({:model_skip, "gradual descr in value model"})

      Val.cons?(v) ->
        case t do
          %{list: bdd} -> eval_bdd(bdd, Val.decompose(v))
          %{} -> false
        end

      true ->
        subtype?(Val.single(v), t)
    end
  end

  # Evaluate a list-component BDD against a decomposed cons value.
  # Node {_, lit, c, u, d} = (lit ∧ c) ∨ u ∨ (¬lit ∧ d); leaves are
  # :bdd_top/:bdd_bot or a literal {_, elem, last}.
  defp eval_bdd(:bdd_top, _vv), do: true
  defp eval_bdd(:bdd_bot, _vv), do: false

  defp eval_bdd({_h, elem, last}, vv), do: eval_literal(elem, last, vv)

  defp eval_bdd({_h, {_lh, elem, last}, c, u, d}, vv) do
    if eval_literal(elem, last, vv) do
      eval_bdd(c, vv) or eval_bdd(u, vv)
    else
      eval_bdd(u, vv) or eval_bdd(d, vv)
    end
  end

  defp eval_bdd(other, _vv), do: throw({:model_skip, "unknown list BDD node: #{inspect(other)}"})

  # A literal {elem, last} contains a non-empty list iff all elements belong to
  # `elem` and the terminator belongs to `last`. Both may be the atom :term.
  defp eval_literal(elem, last, {elems, terminator}) do
    Enum.all?(elems, &member?(&1, elem)) and member?(terminator, last)
  end
end

# ---------------------------------------------------------------------------
# Random descr generators (static fragment + gradual fragment)
# ---------------------------------------------------------------------------

defmodule Gen do
  import Module.Types.Descr

  @atoms [:x, :y, :z]
  @keys [:a, :b, :c]

  # ----- Singletons for the classic membership laws -----
  # (descr generation itself now goes through DescrRecipe, so failures shrink.)
  def singleton(0), do: atom([Enum.random(@atoms)])

  def singleton(depth) do
    case :rand.uniform(4) do
      1 -> atom([Enum.random(@atoms)])
      2 -> empty_list()
      3 -> tuple(for _ <- 1..:rand.uniform(3), do: singleton(depth - 1))
      4 -> closed_map(for k <- Enum.take(@keys, :rand.uniform(3)), do: {k, singleton(depth - 1)})
    end
  end
end

defmodule Laws do
  import Module.Types.Descr

  @nel_top non_empty_list(term(), term())

  # --- Lattice / Boolean-algebra laws over the STATIC fragment ---
  def algebra do
    [
      {"reflexivity: a <= a", fn a, _b, _c -> subtype?(a, a) end},
      {"equal?(a, a)", fn a, _b, _c -> equal?(a, a) end},
      {"inter(a,b) <= a", fn a, b, _c -> subtype?(opt_intersection(a, b), a) end},
      {"a <= union(a,b)", fn a, b, _c -> subtype?(a, opt_union(a, b)) end},
      {"diff(a,b) <= a", fn a, b, _c -> subtype?(opt_difference(a, b), a) end},
      {"inter(diff(a,b), b) is empty",
       fn a, b, _c -> empty?(opt_intersection(opt_difference(a, b), b)) end},
      {"empty?(diff(a,b)) == subtype?(a,b)",
       fn a, b, _c -> empty?(opt_difference(a, b)) == subtype?(a, b) end},
      {"disjoint?(a,b) == empty?(inter(a,b))",
       fn a, b, _c -> disjoint?(a, b) == empty?(opt_intersection(a, b)) end},
      {"union commutative", fn a, b, _c -> equal?(opt_union(a, b), opt_union(b, a)) end},
      {"inter commutative",
       fn a, b, _c -> equal?(opt_intersection(a, b), opt_intersection(b, a)) end},
      {"union associative",
       fn a, b, c -> equal?(opt_union(opt_union(a, b), c), opt_union(a, opt_union(b, c))) end},
      {"inter associative",
       fn a, b, c ->
         equal?(
           opt_intersection(opt_intersection(a, b), c),
           opt_intersection(a, opt_intersection(b, c))
         )
       end},
      {"absorption union(a, inter(a,b)) == a",
       fn a, b, _c -> equal?(opt_union(a, opt_intersection(a, b)), a) end},
      {"absorption inter(a, union(a,b)) == a",
       fn a, b, _c -> equal?(opt_intersection(a, opt_union(a, b)), a) end},
      {"distributivity inter/union",
       fn a, b, c ->
         equal?(
           opt_intersection(a, opt_union(b, c)),
           opt_union(opt_intersection(a, b), opt_intersection(a, c))
         )
       end},
      {"De Morgan: neg(union(a,b)) == inter(neg a, neg b)",
       fn a, b, _c ->
         equal?(opt_negation(opt_union(a, b)), opt_intersection(opt_negation(a), opt_negation(b)))
       end},
      {"double negation", fn a, _b, _c -> equal?(opt_negation(opt_negation(a)), a) end},
      {"excluded middle: union(a, neg a) == term",
       fn a, _b, _c -> equal?(opt_union(a, opt_negation(a)), term()) end},
      {"non-contradiction: inter(a, neg a) empty",
       fn a, _b, _c -> empty?(opt_intersection(a, opt_negation(a))) end},
      {"diff(a,b) == inter(a, neg b)",
       fn a, b, _c -> equal?(opt_difference(a, b), opt_intersection(a, opt_negation(b))) end},
      {"partition: union(inter(a,b), diff(a,b)) == a",
       fn a, b, _c -> equal?(opt_union(opt_intersection(a, b), opt_difference(a, b)), a) end},
      {"diff chain: a\\(b∪c) == (a\\b)\\c",
       fn a, b, c ->
         equal?(
           opt_difference(a, opt_union(b, c)),
           opt_difference(opt_difference(a, b), c)
         )
       end},
      {"diff order: (a\\b)\\c == (a\\c)\\b",
       fn a, b, c ->
         equal?(
           opt_difference(opt_difference(a, b), c),
           opt_difference(opt_difference(a, c), b)
         )
       end},
      {"transitivity: a<=b and b<=c => a<=c",
       fn a, b, c ->
         ab = opt_intersection(a, b)
         bc = opt_union(b, c)
         # ab <= b and b <= bc always; check ab <= bc
         subtype?(ab, bc)
       end}
    ]
  end

  # --- Classic singleton membership laws ---
  def membership do
    [
      {"s <= union(a,b) == (s<=a or s<=b)",
       fn s, a, b -> subtype?(s, opt_union(a, b)) == (subtype?(s, a) or subtype?(s, b)) end},
      {"s <= inter(a,b) == (s<=a and s<=b)",
       fn s, a, b ->
         subtype?(s, opt_intersection(a, b)) == (subtype?(s, a) and subtype?(s, b))
       end},
      {"s <= diff(a,b) == (s<=a and not s<=b)",
       fn s, a, b ->
         subtype?(s, opt_difference(a, b)) == (subtype?(s, a) and not subtype?(s, b))
       end},
      {"s <= neg(a) == (not s<=a)",
       fn s, a, _b -> subtype?(s, opt_negation(a)) == not subtype?(s, a) end}
    ]
  end

  # --- Value-model laws: membership commutes with the boolean algebra ---
  # Args: concrete value v, static descrs a, b.
  def value_ops do
    [
      {"v in union(a,b) == (v in a or v in b)",
       fn v, a, b ->
         Model.member?(v, opt_union(a, b)) == (Model.member?(v, a) or Model.member?(v, b))
       end},
      {"v in inter(a,b) == (v in a and v in b)",
       fn v, a, b ->
         Model.member?(v, opt_intersection(a, b)) ==
           (Model.member?(v, a) and Model.member?(v, b))
       end},
      {"v in diff(a,b) == (v in a and not v in b)",
       fn v, a, b ->
         Model.member?(v, opt_difference(a, b)) ==
           (Model.member?(v, a) and not Model.member?(v, b))
       end},
      {"v in neg(a) == not (v in a)",
       fn v, a, _b -> Model.member?(v, opt_negation(a)) == not Model.member?(v, a) end},
      {"subtype-soundness: a<=b and v in a => v in b",
       fn v, a, b ->
         not (subtype?(a, b) and Model.member?(v, a)) or Model.member?(v, b)
       end},
      {"empty-soundness: empty?(a) => v not in a",
       fn v, a, _b -> not empty?(a) or not Model.member?(v, a) end},
      # One-way cross-validations of the model itself against public API.
      {"model-consistency: enclosing nel <= a => v in a",
       fn v, a, _b ->
         if Val.cons?(v) do
           case enclosing_nel(v) do
             nil -> true
             nel -> not subtype?(nel, a) or Model.member?(v, a)
           end
         else
           true
         end
       end},
      {"model-consistency: v in a => enclosing nel not disjoint from a",
       fn v, a, _b ->
         if Val.cons?(v) do
           case enclosing_nel(v) do
             nil -> true
             nel -> not Model.member?(v, a) or not disjoint?(nel, a)
           end
         else
           true
         end
       end}
    ]
  end

  # Smallest expressible nel type containing cons value v (union of element
  # singletons + terminator singleton). Nil when an element is itself a cons
  # (nested lists have no simple enclosing nel).
  defp enclosing_nel(v) do
    {elems, terminator} = Val.decompose(v)

    if Enum.any?(elems, &Val.cons?/1) do
      nil
    else
      elem_t = Enum.reduce(elems, none(), fn e, acc -> opt_union(Val.single(e), acc) end)
      non_empty_list(elem_t, Val.single(terminator))
    end
  end

  # --- Projection laws driven by the value model ---
  # Args: concrete value v, static descr a (only evaluated when v in a).
  def projections do
    [
      {"list_hd sound: v=[h|_] in a => h in list_hd(a)",
       fn v, a, _b ->
         with true <- Val.cons?(v),
              true <- Model.member?(v, a),
              true <- subtype?(a, @nel_top) do
           case list_hd(a) do
             {:ok, ht} -> Model.member?(hd(v), ht)
             _other -> false
           end
         else
           _ -> true
         end
       end},
      {"list_tl sound: v=[_|t] in a => t in list_tl(a)",
       fn v, a, _b ->
         with true <- Val.cons?(v),
              true <- Model.member?(v, a),
              true <- subtype?(a, @nel_top) do
           case list_tl(a) do
             {:ok, tt} -> Model.member?(tl(v), tt)
             _other -> false
           end
         else
           _ -> true
         end
       end},
      {"tuple_fetch sound: v tuple in a => elem(v,i) in tuple_fetch(a,i)",
       fn v, a, _b ->
         with true <- is_tuple(v) and tuple_size(v) > 0,
              true <- Model.member?(v, a) do
           i = :rand.uniform(tuple_size(v)) - 1

           case tuple_fetch(a, i) do
             {_opt, t} ->
               Model.member?(elem(v, i), t)

             :badindex ->
               # :badindex is only sound if some member lacks index i;
               # if every member has arity > i, it is a false positive.
               not subtype?(a, open_tuple(List.duplicate(term(), i + 1)))

             :badtuple ->
               # v is a member tuple, so a does contain tuples; :badtuple is
               # legitimate when a also has non-tuple parts.
               not subtype?(a, tuple())
           end
         else
           _ -> true
         end
       end},
      {"tuple_insert_at sound: insert(v,i,w) in tuple_insert_at(a,i,s)",
       fn v, a, _b ->
         with true <- is_tuple(v),
              true <- Model.member?(v, a),
              true <- subtype?(a, tuple()) do
           i = :rand.uniform(tuple_size(v) + 1) - 1
           # Insertion at i is only well-defined for members of size >= i; only
           # demand a clean result when ALL members qualify, else any verdict
           # short of a crash is acceptable.
           if i == 0 or subtype?(a, open_tuple(List.duplicate(term(), i))) do
             w = Val.flat(1)
             s = Val.single(w)

             case tuple_insert_at(a, i, s) do
               %{} = r ->
                 inserted = List.to_tuple(List.insert_at(Tuple.to_list(v), i, w))
                 Model.member?(inserted, r)

               :term ->
                 true

               _err ->
                 false
             end
           else
             true
           end
         else
           _ -> true
         end
       end},
      {"tuple_delete_at sound: delete(v,i) in tuple_delete_at(a,i)",
       fn v, a, _b ->
         with true <- is_tuple(v) and tuple_size(v) > 0,
              true <- Model.member?(v, a),
              true <- subtype?(a, tuple()) do
           i = :rand.uniform(tuple_size(v)) - 1

           cond do
             # All members have index i: demand a clean result containing the
             # concrete deletion.
             subtype?(a, open_tuple(List.duplicate(term(), i + 1))) ->
               case tuple_delete_at(a, i) do
                 %{} = r ->
                   deleted = List.to_tuple(List.delete_at(Tuple.to_list(v), i))
                   Model.member?(deleted, r)

                 :term ->
                   true

                 _err ->
                   false
               end

             true ->
               # Some members may lack index i; only require that a returned
               # descr still contains the concrete deletion.
               case tuple_delete_at(a, i) do
                 %{} = r ->
                   deleted = List.to_tuple(List.delete_at(Tuple.to_list(v), i))
                   Model.member?(deleted, r)

                 _other ->
                   true
               end
           end
         else
           _ -> true
         end
       end},
      {"map_fetch_key sound: v map in a, k in v => v[k] in map_fetch_key(a,k)",
       fn v, a, _b ->
         with true <- is_map(v) and map_size(v) > 0,
              true <- Model.member?(v, a) do
           k = Enum.random(Map.keys(v))

           case map_fetch_key(a, k) do
             {_opt, t} ->
               Model.member?(Map.fetch!(v, k), t)

             :badkey ->
               # Only a false positive when every member of a has k required.
               not subtype?(a, open_map([{k, term()}]))

             :badmap ->
               not subtype?(a, open_map())
           end
         else
           _ -> true
         end
       end},
      {"map_put sound: Map.put(v,k,w) in map_put(a,key,val)",
       fn v, a, _b ->
         with true <- is_map(v),
              true <- Model.member?(v, a),
              true <- subtype?(a, open_map()) do
           k = Enum.random([:a, :b, :c])
           w = Val.flat(1)
           # Sometimes a singleton key, sometimes the whole atom() domain --
           # both must produce a result containing the concrete Map.put.
           key_descr = Enum.random([atom([k]), atom()])

           case map_put(a, key_descr, Val.single(w)) do
             {:ok, r} -> Model.member?(Map.put(v, k, w), r)
             _err -> false
           end
         else
           _ -> true
         end
       end}
    ]
  end

  # --- Congruence: equal? types must behave identically under every op ---
  # Args: static descrs a, c (b unused); a2 is rebuilt equal to a.
  def congruence do
    [
      {"congruence: rebuilt a' stays equal?",
       fn a, c, _ ->
         equal?(a, rebuild(a, c)) and equal?(a, opt_negation(opt_negation(a)))
       end},
      {"congruence: binary ops agree on a and a'",
       fn a, c, _ ->
         a2 = rebuild(a, c)

         equal?(opt_union(a, c), opt_union(a2, c)) and
           equal?(opt_intersection(a, c), opt_intersection(a2, c)) and
           equal?(opt_difference(a, c), opt_difference(a2, c)) and
           equal?(opt_difference(c, a), opt_difference(c, a2))
       end},
      {"congruence: empty?/subtype? agree on a and a'",
       fn a, c, _ ->
         a2 = rebuild(a, c)

         empty?(a) == empty?(a2) and subtype?(a, c) == subtype?(a2, c) and
           subtype?(c, a) == subtype?(c, a2)
       end},
      {"congruence: list_hd/list_tl agree on a and a'",
       fn a, c, _ ->
         a2 = rebuild(a, c)
         verdicts_match?(list_hd(a), list_hd(a2)) and verdicts_match?(list_tl(a), list_tl(a2))
       end},
      {"congruence: tuple_fetch agrees on a and a'",
       fn a, c, _ ->
         a2 = rebuild(a, c)
         i = :rand.uniform(3) - 1
         verdicts_match?(tuple_fetch(a, i), tuple_fetch(a2, i))
       end},
      {"congruence: tuple_insert_at agrees on a and a'",
       fn a, c, _ ->
         if empty?(a) do
           true
         else
           a2 = rebuild(a, c)
           i = :rand.uniform(3) - 1
           verdicts_match?(tuple_insert_at(a, i, c), tuple_insert_at(a2, i, c))
         end
       end},
      {"congruence: tuple_delete_at agrees on a and a'",
       fn a, c, _ ->
         if empty?(a) do
           true
         else
           a2 = rebuild(a, c)
           i = :rand.uniform(3) - 1
           verdicts_match?(tuple_delete_at(a, i), tuple_delete_at(a2, i))
         end
       end},
      {"congruence: map_fetch_key agrees on a and a'",
       fn a, c, _ ->
         a2 = rebuild(a, c)
         k = Enum.random([:a, :b, :c])
         verdicts_match?(map_fetch_key(a, k), map_fetch_key(a2, k))
       end},
      {"congruence: map_put agrees on a and a'",
       fn a, c, _ ->
         a2 = rebuild(a, c)
         k = Enum.random([atom([:a]), atom()])
         verdicts_match?(map_put(a, k, c), map_put(a2, k, c))
       end},
      {"congruence: fun_apply agrees on a and a'",
       fn a, c, _ ->
         a2 = rebuild(a, c)
         verdicts_match?(safe_apply(a, [c]), safe_apply(a2, [c]))
       end}
    ]
  end

  # a' == a built through a different construction path, so the two share
  # semantics but not internal representation. Two strategies:
  #   1. partition identity: (a ∩ c) ∪ (a \ c)
  #   2. double difference through a superset cover: cover \ (cover \ a) with
  #      cover = a ∪ c. This turns positively-built types into negation-form
  #      BDDs (and vice versa), which is exactly where representation-sensitive
  #      fast paths (e.g. tuple_insert_at on :bdd_top branches) diverge.
  defp rebuild(a, c) do
    case :rand.uniform(3) do
      1 ->
        opt_union(opt_intersection(a, c), opt_difference(a, c))

      2 ->
        cover = opt_union(a, c)
        opt_difference(cover, opt_difference(cover, a))

      3 ->
        opt_difference(term(), opt_difference(term(), a))
    end
  end

  defp safe_apply(f, args) do
    fun_apply(f, args)
  rescue
    err -> {:raised, err.__struct__}
  end

  # Two op results "match" when they are the same verdict shape and any
  # contained descrs are equal?. Payload descrs must be compared with equal?
  # (never ==): representations may legitimately differ.
  defp verdicts_match?({:ok, t1}, {:ok, t2}), do: equal?(t1, t2)

  defp verdicts_match?({o1, t1}, {o2, t2}) when is_boolean(o1) and is_boolean(o2),
    do: o1 == o2 and equal?(t1, t2)

  defp verdicts_match?({:badarg, ts1}, {:badarg, ts2}), do: descr_lists_equal?(ts1, ts2)

  # fun_apply returns {:badarg, domains, thrown?} on current trees.
  defp verdicts_match?({:badarg, ts1, thrown1}, {:badarg, ts2, thrown2}),
    do: thrown1 == thrown2 and descr_lists_equal?(ts1, ts2)

  defp verdicts_match?({:badarity, a1}, {:badarity, a2}), do: Enum.sort(a1) == Enum.sort(a2)
  defp verdicts_match?(%{} = t1, %{} = t2), do: equal?(t1, t2)
  defp verdicts_match?(:term, t2) when is_map(t2), do: equal?(term(), t2)
  defp verdicts_match?(t1, :term) when is_map(t1), do: equal?(t1, term())
  defp verdicts_match?(v, v), do: true
  defp verdicts_match?(_, _), do: false

  defp descr_lists_equal?(ts1, ts2) do
    length(ts1) == length(ts2) and
      Enum.zip(ts1, ts2) |> Enum.all?(fn {x, y} -> equal?(x, y) end)
  end

  # --- fun_apply relational laws ---
  def funs do
    [
      {"fun_apply(fun([a],r), [a]) returns {:ok, <= r}",
       fn a, r, _c ->
         if empty?(a) do
           true
         else
           case fun_apply(fun([a], r), [a]) do
             {:ok, res} -> subtype?(res, r)
             _other -> false
           end
         end
       end},
      {"fun_apply on narrowed arg stays within r",
       fn a, r, c ->
         arg = opt_intersection(a, c)

         if empty?(a) or empty?(arg) do
           true
         else
           case fun_apply(fun([a], r), [arg]) do
             {:ok, res} -> subtype?(res, r)
             _other -> false
           end
         end
       end}
    ]
  end

  # --- Gradual interval laws (see header note: internal-consistency checks) ---
  def gradual do
    [
      {"gradual invariant: lower_bound(a) <= upper_bound(a)",
       fn a, _b, _c -> subtype?(lower_bound(a), upper_bound(a)) end},
      {"dynamic(a) has empty lower and preserves upper",
       fn a, _b, _c ->
         da = dynamic(a)
         empty?(lower_bound(da)) and equal?(upper_bound(da), upper_bound(a))
       end},
      {"gradual subtype? matches interval subtyping",
       fn a, b, _c ->
         subtype?(a, b) ==
           (subtype?(lower_bound(a), lower_bound(b)) and
              subtype?(upper_bound(a), upper_bound(b)))
       end},
      {"gradual equal? matches interval equality",
       fn a, b, _c ->
         equal?(a, b) ==
           (equal?(lower_bound(a), lower_bound(b)) and
              equal?(upper_bound(a), upper_bound(b)))
       end},
      {"gradual disjoint? matches upper-bound disjointness",
       fn a, b, _c -> disjoint?(a, b) == disjoint?(upper_bound(a), upper_bound(b)) end},
      {"gradual union bounds",
       fn a, b, _c ->
         same_bounds?(
           opt_union(a, b),
           opt_union(lower_bound(a), lower_bound(b)),
           opt_union(upper_bound(a), upper_bound(b))
         )
       end},
      {"gradual intersection bounds",
       fn a, b, _c ->
         same_bounds?(
           opt_intersection(a, b),
           opt_intersection(lower_bound(a), lower_bound(b)),
           opt_intersection(upper_bound(a), upper_bound(b))
         )
       end},
      {"gradual difference bounds",
       fn a, b, _c ->
         same_bounds?(
           opt_difference(a, b),
           opt_difference(lower_bound(a), upper_bound(b)),
           opt_difference(upper_bound(a), lower_bound(b))
         )
       end},
      {"gradual negation bounds",
       fn a, _b, _c ->
         same_bounds?(
           opt_negation(a),
           opt_negation(upper_bound(a)),
           opt_negation(lower_bound(a))
         )
       end},
      {"compatible? matches restricted consistent subtyping",
       fn a, b, _c -> compatible?(a, b) == compatible_formula?(a, b) end},
      {"compatible_intersection matches interval refinement",
       fn a, b, _c -> compatible_intersection_formula?(a, b) end}
    ]
  end

  # --- Totality: public ops and the printer never crash on valid descrs ---
  def total do
    [
      {"boolean ops never crash",
       fn a, b, _c ->
         ok(fn -> opt_union(a, b) end) and ok(fn -> opt_intersection(a, b) end) and
           ok(fn -> opt_difference(a, b) end) and ok(fn -> opt_negation(a) end)
       end},
      {"relations never crash",
       fn a, b, _c ->
         ok(fn -> empty?(a) end) and ok(fn -> subtype?(a, b) end) and
           ok(fn -> disjoint?(a, b) end) and ok(fn -> compatible?(a, b) end)
       end},
      {"projections never crash on non-empty input",
       fn a, _b, c ->
         if empty?(a) do
           true
         else
           ok(fn -> list_hd(a) end) and ok(fn -> list_tl(a) end) and
             ok(fn -> tuple_fetch(a, 1) end) and ok(fn -> tuple_values(a) end) and
             ok(fn -> tuple_insert_at(a, 1, c) end) and ok(fn -> tuple_delete_at(a, 1) end) and
             ok(fn -> map_fetch_key(a, :a) end) and ok(fn -> map_put(a, atom([:a]), c) end) and
             ok(fn -> fun_apply(a, [c]) end)
         end
       end},
      {"to_quoted_string never crashes", fn a, _b, _c -> ok(fn -> to_quoted_string(a) end) end}
    ]
  end

  defp ok(thunk) do
    thunk.()
    true
  rescue
    _ -> false
  end

  defp same_bounds?(actual, lower, upper) do
    equal?(lower_bound(actual), lower) and equal?(upper_bound(actual), upper)
  end

  defp compatible_formula?(left, right) do
    left_lower = lower_bound(left)
    left_upper = upper_bound(left)
    right_upper = upper_bound(right)

    if empty?(left_lower) do
      not empty?(opt_intersection(left_upper, right_upper))
    else
      subtype?(left_lower, right_upper)
    end
  end

  defp compatible_intersection_formula?(left, right) do
    # Empty (uninhabited) `left` is a degenerate case where
    # compatible_intersection/2 and compatible?/2 may deliberately diverge;
    # skip rather than report a false failure.
    if empty?(left) do
      true
    else
      left_lower = lower_bound(left)
      upper_intersection = opt_intersection(upper_bound(left), upper_bound(right))

      case compatible_intersection(left, right) do
        {:ok, actual} ->
          expected_lower = if empty?(left_lower), do: none(), else: left_lower

          compatible_formula?(left, right) and
            same_bounds?(actual, expected_lower, upper_intersection)

        {:error, _} ->
          not compatible_formula?(left, right)
      end
    end
  end
end

# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

defmodule Runner do
  import Module.Types.Descr

  # Operand specs: {:recipe, r} (shrinkable, built via DescrRecipe),
  # {:value, v} (concrete value), {:descr, d} (pre-built, not shrinkable).

  def run(%{seeds: seeds, samples: samples, depth: depth}) do
    IO.puts("descr_fuzz: seeds #{inspect(seeds)}, #{samples} samples/seed, depth #{depth}\n")

    {failures, skips} =
      for seed <- seeds, reduce: {[], 0} do
        {acc, skips} ->
          :rand.seed(:exsss, {seed, seed * 7 + 1, seed * 13 + 3})
          run_seed(seed, samples, depth, acc, skips)
      end

    report(failures, skips)
  end

  defp run_seed(seed, samples, depth, acc, skips) do
    Enum.reduce(1..samples, {acc, skips}, fn i, {acc, skips} ->
      groups = [
        {Laws.algebra(), [mixed(depth), mixed(depth), mixed(depth)]},
        {Laws.membership(), [{:descr, Gen.singleton(depth)}, mixed(depth), mixed(depth)]},
        {Laws.value_ops(), [{:value, Val.value(depth)}, mixed(depth), mixed(depth)]},
        {Laws.projections(), [{:value, Val.projection_value(depth)}, mixed(depth), fuzz(depth)]},
        {Laws.congruence(), [fuzz(depth), fuzz(depth), fuzz(depth)]},
        {Laws.funs(), [fuzz(depth - 1), fuzz(depth - 1), fuzz(depth - 1)]},
        {Laws.gradual(), [gradual(depth), gradual(depth), gradual(depth)]},
        {Laws.total(), [gradual(depth), gradual(depth), gradual(depth)]}
      ]

      Enum.reduce(groups, {acc, skips}, fn {laws, specs}, {acc, skips} ->
        check(acc, skips, laws, specs, seed, i)
      end)
    end)
  end

  defp mixed(depth) do
    recipe =
      case :rand.uniform(8) do
        n when n in 1..2 -> DescrRecipe.biased(:list, depth)
        3 -> DescrRecipe.biased(:tuple, depth)
        4 -> DescrRecipe.biased(:map, depth)
        _ -> DescrRecipe.fuzz_recipe(depth)
      end

    {:recipe, recipe}
  end

  defp fuzz(depth), do: {:recipe, DescrRecipe.fuzz_recipe(max(depth, 0))}
  defp gradual(depth), do: {:recipe, DescrRecipe.fuzz_gradual(depth)}

  defp materialize({:recipe, r}), do: DescrRecipe.build(r)
  defp materialize({:value, v}), do: v
  defp materialize({:descr, d}), do: d

  defp check(acc, skips, laws, specs, seed, i) do
    case try_materialize(specs) do
      {:crash, op, err} ->
        if Enum.any?(acc, &(&1.law == "construction crashed: #{op}")) do
          {acc, skips}
        else
          # Shrink the construction crash itself: keep the smallest spec set
          # whose materialization still crashes.
          small =
            shrink_specs(specs, fn candidate ->
              match?({:crash, _, _}, try_materialize(candidate))
            end)

          {:crash, small_op, small_err} = try_materialize(small)
          _ = {op, err}

          finding = %{
            law: "construction crashed: #{small_op}",
            seed: seed,
            sample: i,
            specs: small,
            result: {:crash, small_err}
          }

          {[finding | acc], skips}
        end

      {:ok, [a, b, c]} ->
        run_laws(acc, skips, laws, specs, a, b, c, seed, i)
    end
  end

  defp try_materialize(specs) do
    {:ok, Enum.map(specs, &materialize/1)}
  catch
    {:recipe_crash, op, _args, err} -> {:crash, op, err}
  end

  defp run_laws(acc, skips, laws, specs, a, b, c, seed, sample) do
    Enum.reduce(laws, {acc, skips}, fn {name, fun}, {acc, skips} ->
      # Some laws draw randomness internally (indices, keys, rebuild
      # strategies). Snapshot the PRNG so shrinking can re-evaluate the law
      # with identical draws.
      rand_state = :rand.export_seed()
      result = eval_law(fun, a, b, c)

      case result do
        true ->
          {acc, skips}

        :model_skip ->
          {acc, skips + 1}

        other ->
          if Enum.any?(acc, &(&1.law == name)) do
            {acc, skips}
          else
            small =
              shrink_specs(specs, fn candidate ->
                :rand.seed(rand_state)

                case try_materialize(candidate) do
                  {:ok, [a2, b2, c2]} -> eval_law(fun, a2, b2, c2) not in [true, :model_skip]
                  {:crash, _, _} -> false
                end
              end)

            finding = %{law: name, seed: seed, sample: sample, specs: small, result: other}
            {[finding | acc], skips}
          end
      end
    end)
  end

  defp eval_law(fun, a, b, c) do
    try do
      fun.(a, b, c)
    rescue
      err -> {:crash, err}
    catch
      {:model_skip, _reason} -> :model_skip
    end
  end

  # Greedy shrink over the recipe positions of a spec list.
  defp shrink_specs(specs, fail?), do: do_shrink(specs, fail?, 500)

  defp do_shrink(specs, fail?, budget) when budget > 0 do
    attempt =
      Enum.reduce_while(0..(length(specs) - 1), nil, fn i, nil ->
        case Enum.at(specs, i) do
          {:recipe, r} ->
            candidate =
              r
              |> DescrRecipe.candidates()
              |> Enum.sort_by(&DescrRecipe.size/1)
              |> Enum.find(fn c ->
                fail?.(List.replace_at(specs, i, {:recipe, c}))
              end)

            case candidate do
              nil -> {:cont, nil}
              c -> {:halt, List.replace_at(specs, i, {:recipe, c})}
            end

          _other ->
            {:cont, nil}
        end
      end)

    case attempt do
      nil -> specs
      smaller -> do_shrink(smaller, fail?, budget - 1)
    end
  end

  defp do_shrink(specs, _fail?, _budget), do: specs

  defp report(failures, skips) do
    if skips > 0 do
      IO.puts("note: #{skips} law evaluations skipped (value model did not apply)\n")
    end

    case failures |> Enum.reverse() |> Enum.uniq_by(& &1.law) do
      [] ->
        IO.puts("PASS -- no law violations found.")
        System.halt(0)

      failures ->
        IO.puts("FAIL -- #{length(failures)} distinct law(s) violated (operands shrunk):\n")

        for f <- Enum.sort_by(failures, & &1.law) do
          IO.puts("* #{f.law}   (seed #{f.seed}, sample #{f.sample})")

          case f.result do
            {:crash, err} ->
              IO.puts("    raised: #{String.replace(Exception.message(err), "\n", " ")}")

            false ->
              IO.puts("    returned false")
          end

          for {label, spec} <- Enum.zip([:a, :b, :c], f.specs) do
            IO.puts("    #{label} = #{render_spec(spec)}")
          end

          IO.puts("")
        end

        System.halt(1)
    end
  end

  defp render_spec({:recipe, r}) do
    source = DescrRecipe.render(r)

    pretty =
      try do
        to_quoted_string(DescrRecipe.build(r))
      rescue
        _ -> "<construction crashes>"
      catch
        {:recipe_crash, _, _, _} -> "<construction crashes>"
      end

    if pretty == source, do: source, else: "#{source}   [= #{pretty}]"
  end

  defp render_spec({:value, v}), do: "value: #{Val.render(v)}"

  defp render_spec({:descr, d}) do
    to_quoted_string(d)
  rescue
    _ -> inspect(d, limit: 20)
  end
end

Runner.run(Args.parse(System.argv()))
