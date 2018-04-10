import tidy.rewrite_search

namespace tidy.rewrite_search.testing

axiom foo' : [6] = [7]
axiom bar' : [[6],[6]] = [[5],[5]]

example : [[7],[6]] = [[5],[5]] :=
begin
 success_if_fail { rewrite_search [] },
-- perform_nth_rewrite_lhs [←foo'] 0,
-- perform_nth_rewrite_lhs [bar'] 0,
 rewrite_search [←foo', bar'],
end

@[search] private axiom foo : [0] = [1]
@[search] private axiom bar1 : [1] = [2]
@[search] private axiom bar2 : [3] = [2]
@[search] private axiom bar3 : [3] = [4]

private example (a : unit) : [[0],[0]] = [[4],[4]] :=
begin
-- perform_nth_rewrite_lhs [foo] 0,
-- perform_nth_rewrite_lhs [bar1] 0,
-- perform_nth_rewrite_lhs [←bar2] 0,
-- perform_nth_rewrite_lhs [foo] 0,
-- perform_nth_rewrite_lhs [bar1] 0,
-- perform_nth_rewrite_lhs [←bar2] 0,
-- perform_nth_rewrite_rhs [←bar3] 0,
-- perform_nth_rewrite_rhs [←bar3] 0,
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
-- perform_nth_rewrite_lhs [bar1] 0,
-- perform_nth_rewrite_lhs [qux'] 0,
-- perform_nth_rewrite_lhs [qux''] 0,
    rewrite_search_using `search,
end

private example : [[0],[0]] = [[4],[4]] :=
begin
-- perform_nth_rewrite_lhs [foo] 0,
-- perform_nth_rewrite_lhs [bar1] 0,
-- perform_nth_rewrite_lhs [←bar2] 0,
-- perform_nth_rewrite_lhs [bar3] 0,
-- perform_nth_rewrite_lhs [foo] 0,
-- perform_nth_rewrite_lhs [bar1] 0,
-- perform_nth_rewrite_lhs [←bar2] 0,
-- perform_nth_rewrite_lhs [bar3] 0,
rewrite_search_using `search,
end

end tidy.rewrite_search.testing