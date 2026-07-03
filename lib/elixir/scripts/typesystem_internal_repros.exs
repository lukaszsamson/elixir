# Combined repro runner for type-system bugs that are not currently reduced to
# ordinary source-level false positives.
#
# Run from the repository root:
#
#     bin/elixir lib/elixir/scripts/typesystem_internal_repros.exs
#
# The script keeps going after crashes and reports whether each known internal
# repro still reproduces on the current checkout.

import Module.Types.Descr

defmodule InternalTypeRepros do
  import Module.Types.Descr

  def run do
    cases()
    |> Enum.map(&run_case/1)
    |> report()
  end

  defp number, do: opt_union(integer(), float())

  defp cases do
    [
      %{
        id: "A2",
        title: "fun_apply on static empty function type crashes",
        expect: :crash,
        run: fn ->
          fun_apply(none(), [integer()])
        end
      },
      %{
        id: "A3",
        title:
          "difference(dynamic(integer()), integer()) leaves %{dynamic: %{}}; negation crashes",
        expect: :crash,
        run: fn ->
          d = opt_difference(dynamic(integer()), integer())
          {d, opt_negation(d)}
        end
      },
      %{
        id: "A4a",
        title: "to_quoted_string crashes on mixed static/dynamic function difference",
        expect: :crash,
        run: fn ->
          fun([term()], atom())
          |> opt_difference(fun([integer()], dynamic(atom())))
          |> to_quoted_string()
        end
      },
      %{
        id: "A4b",
        title:
          "to_quoted_string drops non-function component from mixed static/dynamic function union",
        expect: fn observed -> observed == "(integer() -> atom())" end,
        run: fn ->
          integer()
          |> opt_union(fun([integer()], atom()))
          |> opt_union(dynamic(fun([integer()], atom())))
          |> to_quoted_string()
        end,
        expected: "should include integer() as well as the function type"
      },
      %{
        id: "B2",
        title: "map_put with broad atom key excludes reachable %{a: :x}",
        expect: false,
        run: fn ->
          d = opt_difference(open_map(), empty_map())
          {:ok, res} = map_put(d, atom(), atom([:x]))
          subtype?(closed_map(a: atom([:x])), res)
        end,
        expected: true
      },
      %{
        id: "B3",
        title: "tuple_fetch rejects a type equal to tuple size >= 1",
        expect: :badindex,
        run: fn ->
          t = opt_difference(open_tuple([]), tuple([]))

          unless equal?(t, open_tuple([term()])) do
            raise "setup failed: type no longer equals open_tuple([term()])"
          end

          tuple_fetch(t, 0)
        end,
        expected: "{false, term()}"
      },
      %{
        id: "C1",
        title: "list_tl under-approximates tails through negation",
        expect: false,
        run: fn ->
          t = opt_difference(non_empty_list(atom()), non_empty_list(atom([:a])))
          {:ok, tl} = list_tl(t)
          subtype?(non_empty_list(atom([:a])), tl)
        end,
        expected: true
      },
      %{
        id: "C2",
        title: "list(dynamic()) misses guaranteed empty_list()",
        expect: false,
        run: fn ->
          subtype?(empty_list(), list(dynamic()))
        end,
        expected: true
      },
      %{
        id: "C3",
        title: "@term_or_dynamic_optional breaks subtype transitivity/intersection",
        expect: {true, true, false, true},
        run: fn ->
          t = opt_union(term(), dynamic(not_set()))

          {
            subtype?(term(), t),
            subtype?(dynamic(integer()), term()),
            subtype?(dynamic(integer()), t),
            empty?(opt_intersection(t, dynamic(integer())))
          }
        end,
        expected: "{true, true, true, false}"
      },
      %{
        id: "C4",
        title: "open map with pid domain is not open to bitstring keys",
        expect: false,
        run: fn ->
          s = closed_map([{[:bitstring], atom([:x])}])
          t = open_map([{[:pid], pid()}])
          subtype?(s, t)
        end,
        expected: true
      },
      %{
        id: "C5",
        title: "tuple_insert_at loses inserted element on pure-negative BDD paths",
        expect: true,
        run: fn ->
          t = opt_difference(open_tuple([]), opt_union(tuple([]), tuple([term()])))

          unless equal?(t, open_tuple([term(), term()])) do
            raise "setup failed: type no longer equals open_tuple([term(), term()])"
          end

          inserted = tuple_insert_at(t, 2, float())
          subtype?(tuple([integer(), integer(), atom()]), inserted)
        end,
        expected: false
      },
      %{
        id: "D1",
        title: "difference depends on representation of term() for optional dynamic",
        expect: false,
        run: fn ->
          x = if_set(dynamic(integer()))
          term_map = opt_union(integer(), opt_negation(integer()))
          d1 = opt_difference(x, term())
          d2 = opt_difference(x, term_map)
          equal?(d1, d2)
        end,
        expected: true
      },
      %{
        id: "D2",
        title: "empty function at called arity reports badarity including that arity",
        expect: {true, {:badarity, [1]}},
        run: fn ->
          f =
            fun([number()], atom())
            |> opt_difference(fun([integer()], atom()))

          {empty?(f), fun_apply(f, [integer()])}
        end,
        expected: "{true, :badfun} or another empty-function result"
      },
      %{
        id: "D3",
        title: "list_to_quoted prints negated non-empty list as list()",
        expect: {true, "list(term()) and not list(integer())"},
        run: fn ->
          d = opt_difference(list(term()), non_empty_list(integer()))
          {subtype?(empty_list(), d), to_quoted_string(d)}
        end,
        expected: "{true, \"list(term()) and not non_empty_list(integer())\"}"
      },
      %{
        id: "D4",
        title: "list_of(dynamic()) reports empty_list?: false",
        expect: {false, dynamic()},
        run: fn ->
          list_of(dynamic())
        end,
        expected: "{true, dynamic()}"
      },
      %{
        id: "D5",
        title: ":maps.values badmap path is built with :maps.keys signature",
        expect: true,
        run: fn ->
          source = File.read!("lib/elixir/lib/module/types/apply.ex")

          source =~
            ~r/defp remote_apply\(:maps, :values,.*?badremote\(:maps, :keys,/s
        end,
        expected: "implementation should use badremote(:maps, :values, ...)"
      },
      %{
        id: "D8",
        title: "compatible_intersection succeeds where compatible? rejects",
        expect: {{false, {:ok, none()}}, {false, {:ok, %{dynamic: none()}}}},
        run: fn ->
          bad = %{dynamic: %{}}

          {
            {compatible?(none(), term()), compatible_intersection(none(), term())},
            {compatible?(bad, term()), compatible_intersection(bad, term())}
          }
        end,
        expected: "both compatible_intersection calls should return {:error, left}"
      }
    ]
  end

  defp run_case(%{id: id, title: title, run: fun, expect: expect} = case_info) do
    observed =
      try do
        {:ok, fun.()}
      rescue
        exception -> {:crash, exception}
      catch
        kind, value -> {:throw_or_exit, {kind, value}}
      end

    reproduced? = reproduced?(observed, expect)

    %{
      id: id,
      title: title,
      observed: observed,
      reproduced?: reproduced?,
      expected: Map.get(case_info, :expected)
    }
  end

  defp reproduced?({:crash, _exception}, :crash), do: true
  defp reproduced?({:ok, value}, fun) when is_function(fun, 1), do: fun.(value)
  defp reproduced?({:ok, value}, expected), do: value == expected
  defp reproduced?(_observed, _expected), do: false

  defp report(results) do
    IO.puts("Internal type-system repros")
    IO.puts("===========================\n")

    Enum.each(results, fn result ->
      status = if result.reproduced?, do: "REPRODUCED", else: "NOT REPRODUCED"
      IO.puts("#{status} #{result.id}: #{result.title}")
      IO.puts("  observed: #{format_observed(result.observed)}")

      if result.expected do
        IO.puts("  expected without bug: #{result.expected}")
      end

      IO.puts("")
    end)

    reproduced = Enum.count(results, & &1.reproduced?)
    total = length(results)
    IO.puts("Summary: #{reproduced}/#{total} repros still reproduce.")

    if reproduced == 0, do: System.halt(1), else: System.halt(0)
  end

  defp format_observed({:ok, value}), do: inspect(value, pretty: true, limit: :infinity)

  defp format_observed({:crash, exception}) do
    "#{inspect(exception.__struct__)}: #{Exception.message(exception)}"
  end

  defp format_observed({:throw_or_exit, {kind, value}}) do
    "#{inspect(kind)}: #{inspect(value, pretty: true, limit: :infinity)}"
  end
end

InternalTypeRepros.run()
