import tidy.rewrite_search_2

namespace tidy.rewrite_search.testing

axiom foo' : [6] = [7]
axiom bar' : [[6],[6]] = [[5],[5]]

example : [[7],[6]] = [[5],[5]] :=
begin
    success_if_fail { rewrite_search [] },
    rewrite_search [←foo', bar'] {trace:=tt},
end

@[search] private axiom foo : [0] = [1]
@[search] private axiom bar1 : [1] = [2]
@[search] private axiom bar2 : [3] = [2]
@[search] private axiom bar3 : [3] = [4]

private example (a : unit) : [[0],[0]] = [[4],[4]] :=
begin
    rewrite_search [foo, bar1, ← bar2, bar2, ← bar3],
end

private example : [[0],[0]] = [[4],[4]] :=
begin
    rewrite_search_using `search,
end

@[search] private axiom qux' : [[1], [2]] = [[6], [7]]
@[search] private axiom qux'' : [6] = [7]
private example : [[1], [1]] = [[7], [7]] :=
begin
    rewrite_search_using `search {trace:=tt},
end

end tidy.rewrite_search.testing