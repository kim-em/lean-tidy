import tidy.rewrite_search.engine

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

namespace tidy.rewrite_search.strategy.edit_distance

variables {α : Type} [decidable_eq α]

meta structure ed_searchstate :=
  (dummy : ℕ)

@[derive decidable_eq]
structure ed_partial := 
  (prefix_length : ℕ)
  (suffix    : list string)
  (distances : list ℕ) -- distances from the prefix of l₁ to each non-empty prefix of l₂

def empty_partial_edit_distance_data (l₁ l₂: list string) : ed_partial :=
  ⟨ 0, l₁, (list.range l₂.length).map(λ n, n + 1) ⟩

meta def ed_searchstate_init : ed_searchstate := ⟨ 1 ⟩

meta def ed_step (g : global_state ed_searchstate ed_partial) (itr : ℕ)
  : global_state ed_searchstate ed_partial × (@strategy_action ed_searchstate ed_partial) :=
  if itr <= 10 then
    match g.interesting_pairs with
    | [] := (g, strategy_action.abort "all interesting pairs exhausted!")
    | (best_p :: rest) :=
      let vl := g.get_vertex (best_p.side side.L) in
      let s : side := if itr % 2 = 0 ∧ ¬vl.visited then side.L else side.R in
      (g, strategy_action.examine best_p s)
    end
  else
    (g, strategy_action.abort "max iterations reached")

meta def ed_init_bound (l r : vertex) : @bound_progress ed_partial :=
  at_least 0 (empty_partial_edit_distance_data l.tokens r.tokens)

def triples {α : Type} (p : ed_partial) (l₂ : list α): list (ℕ × ℕ × α) := p.distances.zip ((p.prefix_length :: p.distances).zip l₂)

--FIXME rewrite me
meta def fold_fn (h : string) (n : ℕ × list ℕ) (t : ℕ × ℕ × string) := 
  let m := (if h = t.2.2 then t.2.1 else 1 + min (min (t.2.1) (t.1)) n.2.head) in 
  (min m n.1, m :: n.2)

--FIXME rewrite me
meta def ed_improve_bound_once (l r : list string) (cur : ℕ) (p : ed_partial) : @bound_progress ed_partial :=
  match p.suffix with
    | [] := exactly p.distances.ilast
    | (h :: t) :=
      let initial := (p.prefix_length + 1, [p.prefix_length + 1]) in
      let new_distances : ℕ × list ℕ := (triples p r).foldl (fold_fn h) initial in
      at_least new_distances.1 ⟨ p.prefix_length + 1, t, new_distances.2.reverse.drop 1 ⟩
  end 

meta def ed_improve_bound_over (l r : list string) (m : ℕ) : @bound_progress ed_partial → @bound_progress ed_partial
| (exactly n) := exactly n
| (at_least n p) :=
  if n > m then
    at_least n p
  else
    ed_improve_bound_over (ed_improve_bound_once l r n p)

meta def ed_improve_estimate_over (m : ℕ) (l r : vertex) (bnd : @bound_progress ed_partial) : @bound_progress ed_partial :=
  ed_improve_bound_over l.tokens r.tokens m bnd

end tidy.rewrite_search.strategy.edit_distance

namespace tidy.rewrite_search.strategy

open tidy.rewrite_search.strategy.edit_distance

meta def edit_distance_strategy : @strategy ed_searchstate ed_partial :=
  ⟨ ed_searchstate_init, ed_step, ed_init_bound, ed_improve_estimate_over ⟩

end tidy.rewrite_search.strategy