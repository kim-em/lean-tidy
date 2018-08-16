import tidy.rewrite_search.engine

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

namespace tidy.rewrite_search.strategy.edit_distance

variables {α : Type} [decidable_eq α]

meta structure ed_searchstate :=
  (goal_side : side)

@[derive decidable_eq]
structure ed_partial := 
  (distance : ℕ)

def empty_partial_edit_distance_data (l₁ l₂: list string) : ed_partial :=
  ⟨ ((l₁.zip l₂).filter(λ p : string × string, p.1 = p.2)).length ⟩ 

meta def ed_searchstate_init : ed_searchstate := ⟨ side.L ⟩

meta def ed_step (g : global_state ed_searchstate ed_partial) (itr : ℕ)
  : global_state ed_searchstate ed_partial × (@strategy_action ed_searchstate ed_partial) :=
  if itr <= 500 then
    match g.interesting_pairs with
    | [] := (g, strategy_action.abort "all interesting pairs exhausted!")
    | (best_p :: rest) :=
      let goal_side : side := g.internal_strat_state.goal_side in
      let v := g.get_vertex (best_p.side goal_side) in
      let goal_side : side := if ¬v.visited then goal_side else goal_side.other in
      let g := g.mutate_strategy ⟨ goal_side.other ⟩ in
      (g, strategy_action.examine best_p goal_side)
    end
  else
    (g, strategy_action.abort "max iterations reached")

meta def ed_init_bound (l r : vertex) : bound_progress ed_partial :=
  at_least 0 (empty_partial_edit_distance_data l.tokens r.tokens)

--FIXME rewrite me
meta def ed_improve_bound_once (l r : list string) (cur : ℕ) (p : ed_partial) : bound_progress ed_partial :=
exactly p.distance p

meta def ed_improve_bound_over (l r : list string) (m : ℕ) : bound_progress ed_partial → bound_progress ed_partial
| (exactly n p) := exactly n p
| (at_least n p) :=
  if n > m then
    at_least n p
  else
    ed_improve_bound_over (ed_improve_bound_once l r n p)

meta def ed_improve_estimate_over (m : ℕ) (l r : vertex) (bnd : bound_progress ed_partial) : bound_progress ed_partial :=
  ed_improve_bound_over l.tokens r.tokens m bnd

end tidy.rewrite_search.strategy.edit_distance

namespace tidy.rewrite_search.strategy

open tidy.rewrite_search.strategy.edit_distance

meta def edit_distance_strategy : strategy ed_searchstate ed_partial :=
  ⟨ ed_searchstate_init, ed_step, ed_init_bound, ed_improve_estimate_over ⟩

end tidy.rewrite_search.strategy