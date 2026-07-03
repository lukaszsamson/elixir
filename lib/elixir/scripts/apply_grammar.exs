# Shared typed-program grammar for the type-checker harnesses.
#
# Generates Elixir modules that are WELL-TYPED BY CONSTRUCTION, each function
# carrying runtime WITNESSES: concrete inputs whose expected clause is known
# at generation time (clause bodies return {tag, value} so the reached clause
# is observable). Used by:
#   * apply_fuzz.exs      -- compiles + executes, hunting checker false
#                            positives and crashes
#   * infer_soundness.exs -- compiles, then validates the INFERRED signatures
#                            in the "ExCk" chunk against the witnesses
#
# Loaded with Code.require_file/1; defines Expr, Feature and Build.

defmodule Expr do
  # gen(type, depth, vars) -> source string of that type, total by construction.
  # vars: %{name => type}, types: :integer | :float | :binary | :int_list

  def gen(t, d, vars \\ %{})

  def gen(:integer, 0, vars), do: leaf(:integer, vars)

  def gen(:integer, d, vars) do
    case :rand.uniform(9) do
      1 -> "(#{gen(:integer, d - 1, vars)} + #{gen(:integer, d - 1, vars)})"
      2 -> "(#{gen(:integer, d - 1, vars)} * #{gen(:integer, d - 1, vars)})"
      3 -> "abs(#{gen(:integer, d - 1, vars)})"
      4 -> "div(#{gen(:integer, d - 1, vars)}, #{Enum.random([2, 3, 7])})"
      5 -> "byte_size(#{gen(:binary, d - 1, vars)})"
      6 -> "length(#{gen(:int_list, d - 1, vars)})"
      7 -> "Enum.sum(#{gen(:int_list, d - 1, vars)})"
      8 -> "round(#{gen(:float, d - 1, vars)})"
      9 -> leaf(:integer, vars)
    end
  end

  def gen(:float, 0, vars), do: leaf(:float, vars)

  def gen(:float, d, vars) do
    case :rand.uniform(4) do
      1 -> "(#{gen(:float, d - 1, vars)} + #{gen(:float, d - 1, vars)})"
      2 -> "(#{gen(:integer, d - 1, vars)} / #{Enum.random([2, 4])})"
      3 -> "Float.round(#{gen(:float, d - 1, vars)}, 2)"
      4 -> leaf(:float, vars)
    end
  end

  def gen(:binary, 0, vars), do: leaf(:binary, vars)

  def gen(:binary, d, vars) do
    case :rand.uniform(5) do
      1 -> "(#{gen(:binary, d - 1, vars)} <> #{gen(:binary, d - 1, vars)})"
      2 -> "String.upcase(#{gen(:binary, d - 1, vars)})"
      3 -> "Integer.to_string(#{gen(:integer, d - 1, vars)})"
      4 -> "String.trim(#{gen(:binary, d - 1, vars)})"
      5 -> leaf(:binary, vars)
    end
  end

  def gen(:int_list, 0, vars), do: leaf(:int_list, vars)

  def gen(:int_list, d, vars) do
    case :rand.uniform(5) do
      1 -> "[#{gen(:integer, d - 1, vars)} | #{gen(:int_list, d - 1, vars)}]"
      2 -> "Enum.map(#{gen(:int_list, d - 1, vars)}, fn z -> z + 1 end)"
      3 -> "Enum.sort(#{gen(:int_list, d - 1, vars)})"
      4 -> "(#{gen(:int_list, d - 1, vars)} ++ #{gen(:int_list, d - 1, vars)})"
      5 -> leaf(:int_list, vars)
    end
  end

  defp leaf(t, vars) do
    named = for {n, vt} <- vars, vt == t, do: n

    if named != [] and :rand.uniform(2) == 1 do
      Enum.random(named)
    else
      literal(t)
    end
  end

  defp literal(:integer), do: Integer.to_string(Enum.random(-9..9))
  defp literal(:float), do: Float.to_string(Enum.random(1..9) / 2)
  defp literal(:binary), do: inspect(Enum.random(["", "a", "foo"]))

  defp literal(:int_list) do
    case :rand.uniform(3) do
      1 -> "[]"
      n -> "[" <> Enum.map_join(1..n, ", ", fn _ -> literal(:integer) end) <> "]"
    end
  end

  def sample(:integer), do: Enum.random(-9..9)
  def sample(:float), do: Enum.random(1..9) / 2
  def sample(:binary), do: Enum.random(["", "a", "foo"])
  def sample(:int_list), do: for(_ <- 1..:rand.uniform(3), do: Enum.random(0..9))
end

# ---------------------------------------------------------------------------
# Feature grammar
# ---------------------------------------------------------------------------
#
# Each feature returns:
#   %{
#     src: iodata of defs,
#     witnesses: [{fun_atom, args, expect}],   # expect: {:tag, n} | :any
#     wrappable: nil | {fun_atom, args_src, guard_src, body_src, witnesses}
#   }
# Every clause/branch body returns {tag, value}; each witness's expected tag is
# known, so redundant/never-match warnings are refutable at runtime.

defmodule Feature do
  def random(k) do
    gens = [
      &multi_clause/1,
      &multi_clause/1,
      &case_narrowing/1,
      &binary_construct/1,
      &binary_match/1,
      &closures/1,
      &helper_chain/1,
      &struct_use/1,
      &protocol_impl/1,
      &comprehension/1,
      &with_try/1,
      &map_update/1,
      &string_pattern/1,
      &leaf_expr/1,
      &cond_narrowing/1,
      &repeated_var/1
    ]

    Enum.random(gens).(k)
  end

  # -- F0: repeated variables across patterns (equality constraints). A bound
  # variable in a binary pattern only matches EQUAL binaries, so the guarded
  # clause below is reachable -- historically misjudged as redundant.
  defp repeated_var(k) do
    f = "rv#{k}"

    variant = :rand.uniform(3)

    {src, wits} =
      case variant do
        1 ->
          {"""
             def #{f}(x, <<x::binary>>), do: {0, x}
             def #{f}(a, b) when is_binary(a) and is_binary(b), do: {1, a <> b}
           """,
           [
             {String.to_atom(f), ["s", "s"], {:tag, 0}},
             {String.to_atom(f), ["a", "b"], {:tag, 1}}
           ]}

        2 ->
          {"""
             def #{f}({x, x}) when is_integer(x), do: {0, x}
             def #{f}({a, b}) when is_integer(a) and is_integer(b), do: {1, a + b}
           """,
           [
             {String.to_atom(f), [{3, 3}], {:tag, 0}},
             {String.to_atom(f), [{1, 2}], {:tag, 1}}
           ]}

        3 ->
          {"""
             def #{f}(%{a: v, b: v}), do: {0, v}
             def #{f}(%{a: v, b: w}), do: {1, {v, w}}
           """,
           [
             {String.to_atom(f), [%{a: 1, b: 1}], {:tag, 0}},
             {String.to_atom(f), [%{a: 1, b: 2}], {:tag, 1}}
           ]}
      end

    %{src: [src], witnesses: wits, wrappable: nil}
  end

  # -- F1: multi-clause def over disjoint patterns (pattern subtraction) --
  defp multi_clause(k) do
    f = "mc#{k}"

    # Draw a set of structurally disjoint clauses; literals first, guarded
    # catch-kinds last, so no clause is genuinely redundant.
    # Entries: {pattern, guard-or-nil, body, witness_args, tag}
    literal_pool = [
      {":x", nil, "{0, :x}", [:x], 0},
      {":y", nil, "{1, :y}", [:y], 1},
      {"{:t, s}", "is_binary(s)", "{2, byte_size(s)}", [{:t, "b"}], 2},
      {"[]", nil, "{3, :empty}", [[]], 3},
      {"%{a: v}", "is_integer(v)", "{4, v + 1}", [%{a: 5}], 4}
    ]

    guard_pool = [
      {"n", "is_integer(n)", "{5, n + 1}", [7], 5},
      {"x", "is_float(x)", "{6, x + 1.0}", [1.5], 6},
      {"[h | _]", "is_integer(h)", "{7, h}", [[9, 1]], 7},
      {"b", "is_binary(b)", "{8, byte_size(b)}", ["ab"], 8}
    ]

    lits = Enum.take_random(literal_pool, :rand.uniform(3))
    guards = Enum.take_random(guard_pool, :rand.uniform(3))

    render = fn {pat, g, body, args, tag} ->
      head = if g, do: "def #{f}(#{pat}) when #{g}", else: "def #{f}(#{pat})"
      {"  #{head}, do: #{body}\n", {String.to_atom(f), args, {:tag, tag}}}
    end

    lit_defs = Enum.map(lits, render)
    guard_defs = Enum.map(guards, render)

    # Avoid guard clauses whose kind collides with a literal clause pattern
    # that would shadow it into unreachability... none do: atoms :x/:y vs
    # is_integer/is_float/list/binary are disjoint; [] vs [h|_] disjoint;
    # %{a: _} map clause vs others disjoint.
    {defs, wits} = Enum.unzip(lit_defs ++ guard_defs)
    %{src: defs, witnesses: wits, wrappable: nil}
  end

  # -- F2: case narrowing over a union-typed param --
  defp case_narrowing(k) do
    f = "cn#{k}"

    body = """
      case p do
        q when is_integer(q) -> {0, q + #{Enum.random(1..3)}}
        q when is_atom(q) -> {1, Atom.to_string(q)}
      end
    """

    src = """
      def #{f}(p) when is_integer(p) or is_atom(p) do
    #{body}
      end
    """

    wits = [
      {String.to_atom(f), [Enum.random(1..9)], {:tag, 0}},
      {String.to_atom(f), [Enum.random([:x, :y])], {:tag, 1}}
    ]

    %{
      src: [src],
      witnesses: wits,
      wrappable: {f, "p", "is_integer(p) or is_atom(p)", body, wits}
    }
  end

  # -- F2b: cond narrowing --
  defp cond_narrowing(k) do
    f = "cd#{k}"

    src = """
      def #{f}(p) when is_integer(p) or is_binary(p) do
        cond do
          is_integer(p) -> {0, p * 2}
          is_binary(p) -> {1, p <> "!"}
        end
      end
    """

    %{
      src: [src],
      witnesses: [
        {String.to_atom(f), [3], {:tag, 0}},
        {String.to_atom(f), ["s"], {:tag, 1}}
      ],
      wrappable: nil
    }
  end

  # -- F3: binary construction with size/unit/endianness specifiers --
  defp binary_construct(k) do
    f = "bc#{k}"

    int_specs = ["8", "16", "16-little", "32-big", "size(#{Enum.random(1..12)})", "8-signed"]
    float_specs = ["float", "float-32", "float-64", "float-little"]

    segments =
      Enum.map(1..:rand.uniform(4), fn _ ->
        case :rand.uniform(4) do
          1 -> "i::#{Enum.random(int_specs)}"
          2 -> "f::#{Enum.random(float_specs)}"
          3 -> "#{Enum.random([65, 97])}::utf8"
          4 -> inspect(Enum.random(["ab", "q"]))
        end
      end)

    # a trailing unsized binary segment is only legal last
    segments = segments ++ ["b::binary"]

    src = """
      def #{f}(i, f, b) when is_integer(i) and is_float(f) and is_binary(b) do
        {0, <<#{Enum.join(segments, ", ")}>>}
      end
    """

    %{
      src: [src],
      witnesses: [{String.to_atom(f), [Enum.random(0..200), 1.5, "tail"], {:tag, 0}}],
      wrappable: nil
    }
  end

  # -- F4: binary pattern matching (round-trip witnesses) --
  defp binary_match(k) do
    f = "bm#{k}"
    n1 = Enum.random(0..255)
    n2 = Enum.random(0..65535)

    src = """
      def #{f}(<<a::8, b::16-big, rest::binary>>), do: {0, {a, b, rest}}
      def #{f}(other) when is_binary(other), do: {1, other}
      def #{f}(other) when is_bitstring(other), do: {2, bit_size(other)}
    """

    %{
      src: [src],
      witnesses: [
        {String.to_atom(f), [<<n1::8, n2::16-big, "xy">>], {:tag, 0}},
        {String.to_atom(f), [<<1>>], {:tag, 1}},
        {String.to_atom(f), [<<3::3>>], {:tag, 2}}
      ],
      wrappable: nil
    }
  end

  # -- F5: closures with guard clauses, higher-order use --
  defp closures(k) do
    f = "cl#{k}"

    src = """
      def #{f}(n) when is_integer(n) do
        g = fn
          x when is_integer(x) -> x + 1
          x when is_binary(x) -> byte_size(x)
        end

        {0, g.(n) + g.("ab") + Enum.sum(Enum.map([1, 2, 3], g))}
      end
    """

    %{src: [src], witnesses: [{String.to_atom(f), [4], {:tag, 0}}], wrappable: nil}
  end

  # -- F6: local helper chain (inference across defs) --
  defp helper_chain(k) do
    f = "hc#{k}"
    h = "h#{k}"
    t = Enum.random([:integer, :binary])

    {guard, hbody, arg} =
      case t do
        :integer -> {"is_integer(x)", "x * 2", Enum.random(1..9)}
        :binary -> {"is_binary(x)", "x <> x", "ab"}
      end

    combine =
      case t do
        :integer -> "#{h}(y) + #{h}(3)"
        :binary -> "byte_size(#{h}(y)) + byte_size(#{h}(\"z\"))"
      end

    src = """
      defp #{h}(x) when #{guard}, do: #{hbody}
      def #{f}(y) when #{guard(t, "y")}, do: {0, #{combine}}
    """

    %{src: [src], witnesses: [{String.to_atom(f), [arg], {:tag, 0}}], wrappable: nil}
  end

  defp guard(:integer, v), do: "is_integer(#{v})"
  defp guard(:binary, v), do: "is_binary(#{v})"

  # -- F7: struct definition, construction, access, update, match --
  defp struct_use(k) do
    f = "st#{k}"

    src = """
      def #{f}(n) when is_integer(n) do
        s = %__MODULE__{a: n}
        s2 = %{s | a: s.a + 1, b: "up"}

        case s2 do
          %__MODULE__{a: a, b: b} when is_integer(a) and is_binary(b) -> {0, a + byte_size(b)}
        end
      end
    """

    %{src: [src], witnesses: [{String.to_atom(f), [5], {:tag, 0}}], wrappable: nil}
  end

  # -- F8: protocol + defimpl (incl. the Erlang-module target class) --
  defp protocol_impl(k) do
    # Targets we can also dispatch on at runtime, with a witness value.
    dispatchable = [
      {"Integer", 42},
      {"Atom", :w},
      {"List", [1]},
      {"BitString", "s"},
      {"Map", %{}},
      {"Tuple", {1}}
    ]

    # Compile-only targets: structs and non-struct modules (incl. Erlang
    # modules, which the checker must not crash on).
    compile_only = ["URI", "Date", ":gen_server", ":lists", ":queue"]

    if :rand.uniform(3) == 1 do
      target = Enum.random(compile_only)

      src = """
        defprotocol PF#{k} do
          def go(x)
        end

        defimpl PF#{k}, for: #{target} do
          def go(x), do: x
        end
      """

      %{src: [src], witnesses: [], wrappable: nil}
    else
      {target, value} = Enum.random(dispatchable)
      f = "pr#{k}"

      src = """
        defprotocol PF#{k} do
          def go(x)
        end

        defimpl PF#{k}, for: #{target} do
          def go(x), do: x
        end

        def #{f}(v), do: {0, PF#{k}.go(v)}
      """

      %{src: [src], witnesses: [{String.to_atom(f), [value], {:tag, 0}}], wrappable: nil}
    end
  end

  # -- F9: comprehensions with filters and patterns --
  defp comprehension(k) do
    f = "cp#{k}"

    variant = :rand.uniform(3)

    {src, wit} =
      case variant do
        1 ->
          {"""
             def #{f}(l) when is_list(l) do
               {0, for(x <- l, is_integer(x), do: x + 1)}
             end
           """, {String.to_atom(f), [[1, :a, 2]], {:tag, 0}}}

        2 ->
          {"""
             def #{f}(l) when is_list(l) do
               {0, for({:p, x} <- l, do: x * 2)}
             end
           """, {String.to_atom(f), [[{:p, 1}, :skip, {:p, 3}]], {:tag, 0}}}

        3 ->
          {"""
             def #{f}(l) when is_list(l) do
               {0, for(x <- l, is_integer(x), into: %{}, do: {x, x + 1})}
             end
           """, {String.to_atom(f), [[1, 2]], {:tag, 0}}}
      end

    %{src: [src], witnesses: [wit], wrappable: nil}
  end

  # -- F10: with / try --
  defp with_try(k) do
    f = "wt#{k}"

    src = """
      defp ok#{k}(x) when is_integer(x), do: {:ok, x}
      defp any#{k}(x), do: if(rem(x, 2) == 0, do: {:ok, x}, else: :odd)

      def #{f}(x) when is_integer(x) do
        r =
          with {:ok, y} <- any#{k}(x),
               {:ok, z} <- ok#{k}(y + 1) do
            z
          else
            :odd -> 0
          end

        t =
          try do
            div(x, 2)
          rescue
            ArithmeticError -> -1
          end

        {0, r + t}
      end
    """

    %{
      src: [src],
      witnesses: [
        {String.to_atom(f), [4], {:tag, 0}},
        {String.to_atom(f), [3], {:tag, 0}}
      ],
      wrappable: nil
    }
  end

  # -- F11: map update / access --
  defp map_update(k) do
    f = "mu#{k}"

    src = """
      def #{f}(%{a: x} = m) when is_integer(x) do
        m2 = %{m | a: x + 1}
        m3 = Map.put(m2, :b, "v")
        {0, m3.a + map_size(m3)}
      end
    """

    %{
      src: [src],
      witnesses: [{String.to_atom(f), [%{a: 1}], {:tag, 0}}],
      wrappable: nil
    }
  end

  # -- F12: string prefix patterns --
  defp string_pattern(k) do
    f = "sp#{k}"

    src = """
      def #{f}("pre" <> rest), do: {0, rest}
      def #{f}(s) when is_binary(s), do: {1, s}
    """

    %{
      src: [src],
      witnesses: [
        {String.to_atom(f), ["prefix"], {:tag, 0}},
        {String.to_atom(f), ["other"], {:tag, 1}}
      ],
      wrappable: nil
    }
  end

  # -- F13: deep well-typed leaf expression (v1 style) --
  defp leaf_expr(k) do
    f = "le#{k}"
    t = Enum.random([:integer, :binary, :int_list])

    params =
      Enum.take_random([{"p1", :integer}, {"p2", :binary}, {"p3", :int_list}], :rand.uniform(2))

    vars = Map.new(params, fn {n, pt} -> {n, pt} end)
    body = Expr.gen(t, 3, vars)
    names = Enum.map_join(params, ", ", &elem(&1, 0))
    guards = Enum.map_join(params, " and ", fn {n, pt} -> guard_of(pt, n) end)
    guards = if guards == "", do: "true", else: guards
    args = Enum.map(params, fn {_, pt} -> Expr.sample(pt) end)

    src = """
      def #{f}(#{names}) when #{guards} do
        {0, #{body}}
      end
    """

    wits = [{String.to_atom(f), args, {:tag, 0}}]
    %{src: [src], witnesses: wits, wrappable: {f, names, guards, "{0, #{body}}", wits}}
  end

  defp guard_of(:integer, v), do: "is_integer(#{v})"
  defp guard_of(:binary, v), do: "is_binary(#{v})"
  defp guard_of(:int_list, v), do: "is_list(#{v})"
end

# ---------------------------------------------------------------------------
# Module assembly + metamorphic variants
# ---------------------------------------------------------------------------

defmodule Build do
  def assemble(mod, features) do
    needs_struct? =
      Enum.any?(features, fn f ->
        f.src |> IO.iodata_to_binary() |> String.contains?("%__MODULE__{")
      end)

    struct_def = if needs_struct?, do: "  defstruct a: 0, b: \"s\"\n", else: ""

    src =
      "defmodule #{mod} do\n" <>
        struct_def <>
        IO.iodata_to_binary(Enum.map(features, & &1.src)) <>
        "end\n"

    %{
      mod: mod,
      src: src,
      witnesses: Enum.flat_map(features, & &1.witnesses),
      wrappables: Enum.reject(Enum.map(features, & &1.wrappable), &is_nil/1)
    }
  end

  # Re-render a wrappable def with a semantics-preserving wrapper around its
  # body: same runtime meaning, different syntax tree for the checker.
  def variant(mod, {f, args_src, guard_src, body, wits}) do
    wrapped =
      case :rand.uniform(3) do
        1 -> "(fn -> #{body} end).()"
        2 -> "case :ok do\n      :ok -> #{body}\n    end"
        3 -> "#{body} |> then(& &1)"
      end

    src = """
    defmodule #{mod} do
      def #{f}(#{args_src}) when #{guard_src} do
        #{wrapped}
      end
    end
    """

    %{mod: mod, src: src, witnesses: wits, wrappables: []}
  end
end

# ---------------------------------------------------------------------------
# Runner: compile -> classify diagnostics -> execute witnesses -> oracles
# ---------------------------------------------------------------------------
