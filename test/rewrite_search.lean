-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.rewrite_search

namespace tidy.test

open tactic

def f (x y : ℕ) := x + y
def g (x y : ℕ) := x + y
@[search] lemma h (x y : ℕ) : f x y = g x y := by refl

example : f (g 1 0) 2 = g (f 1 0) 2 :=
begin
target >>= all_rewrites_using `search >>= tactic.trace,
refl
end

def f' {α} (x y : α) := (x, y)
def g' {α} (x y : α) := (x, y)
@[search] lemma h' {α} (x y : α) : f' x y = g' x y := by refl

example : f' (g' 1 0) (2, 3) = g' (f' 1 0) (2, 3) :=
begin
target >>= all_rewrites_using `search >>= tactic.trace,
refl
end

@[search] axiom b (l : list ℕ) : 1 :: l = 2 :: l

example (f : ℕ → list ℕ → Type) : f 3 [1,1,1,2,1] = f 3 [1,2,1,2,1] :=
begin
target >>= all_rewrites_using `search >>= tactic.trace,
perform_nth_rewrite_using `search 5,
refl
end

open tactic.interactive

#eval (breadth_first_search (λ p : ℕ × ℕ, [(p.1+1,p.2),(p.1,p.2+1)]) (0,0) 15).traversed_vertices.map(λ v : traversed_vertex_data (ℕ × ℕ) (ℕ × ℕ) ℕ, v.data.data)
#eval (breadth_first_search (λ p : ℕ × ℕ, [(p.1+1,p.2),(p.1,p.2+1)]) (0,0) 15).untraversed_vertices.map(λ v : untraversed_vertex_data (ℕ × ℕ) (ℕ × ℕ) ℕ, v.data.data)

#eval (depth_first_search (λ p : ℕ × ℕ, [(p.1+1,p.2),(p.1,p.2+1)]) (0,0) 15).traversed_vertices.map(λ v : traversed_vertex_data (ℕ × ℕ) (ℕ × ℕ) ℕ, v.data.data)

-- knights' moves
def knights := (λ p : ℤ × ℤ, [(p.1+2,p.2+1),(p.1+2,p.2-1),(p.1-2,p.2+1),(p.1-2,p.2-1),(p.1+1,p.2+2),(p.1+1,p.2-2),(p.1-1,p.2+2),(p.1-1,p.2-2)])
#eval (breadth_first_search knights (0,0) 20).traversed_vertices.map(λ v : traversed_vertex_data (ℤ × ℤ) (ℤ × ℤ) ℕ, (v.data.data, v.data.descent_data))
#eval (depth_first_search knights (0,0) 20).traversed_vertices.map(λ v : traversed_vertex_data (ℤ × ℤ) (ℤ × ℤ) ℕ, (v.data.data, v.data.descent_data))


@[ematch] private axiom foo : [0] = [1]
@[ematch] private axiom bar1 : [1] = [2]
@[ematch] private axiom bar2 : [3] = [2]
@[ematch] private axiom bar3 : [3] = [4]

private example (a : unit) : [[0],[0]] = [[4],[4]] :=
begin
rewrite_search [foo, bar1, ← bar2, bar2, ← bar3],
end

private example : [[0],[0]] = [[4],[4]] :=
begin
rewrite_search_using `ematch,
end

@[ematch] private axiom qux' : [[1], [2]] = [[6], [7]]
@[ematch] private axiom qux'' : [6] = [7]

private example : [[0],[0]] = [[4],[4]] :=
begin
rewrite_search_using `ematch,
end

private example : [[1], [1]] = [[7], [7]] :=
begin
rewrite_search_using `ematch {trace_result:=tt},
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