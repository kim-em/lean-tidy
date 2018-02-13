import tidy.rewrite_search

namespace tidy.test

open tactic.interactive

@[ematch] private axiom foo : [0] = [1]
@[ematch] private axiom bar1 : [1] = [2]
@[ematch] private axiom bar2 : [3] = [2]
@[ematch] private axiom bar3 : [3] = [4]

private example : [[0],[0]] = [[4],[4]] :=
begin
rewrite_search [foo, bar1, ← bar2, bar2, ← bar3],
end

private example : [[0],[0]] = [[4],[4]] :=
begin
rewrite_search_using `ematch,
end

private axiom qux : [[0],[0]] = [[4],[5]]

private example : [[0],[0]] = [[4],[5]] :=
begin
success_if_fail { rewrite_search_using `ematch },
exact qux
end

@[ematch] private axiom foo' (n : ℕ) : [n, n] = [n+1, n+1]

private example : [0,0] = [1,1] :=
begin
rewrite_search_using `ematch,
end

end tidy.test