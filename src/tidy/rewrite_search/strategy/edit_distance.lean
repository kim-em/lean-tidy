import tidy.rewrite_search.engine

import data.rat

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

namespace tidy.rewrite_search.edit_distance

variables {α : Type} [decidable_eq α]

@[derive decidable_eq]
structure ed_partial :=
  (prefix_length : ℚ)
  (suffix    : list table_ref)
  (distances : list ℚ) -- distances from the prefix of l₁ to each non-empty prefix of l₂

def get_weight (weights : table ℚ) (r : table_ref) : ℚ := max (weights.at r) 1

def compute_initial_distances_aux (weights : table ℚ) : ℚ → list table_ref → list ℚ
| _ [] := []
| so_far (a :: rest) :=
  let so_far := so_far + (get_weight weights a) in
  list.cons so_far (compute_initial_distances_aux so_far rest)

def compute_initial_distances (weights : table ℚ) (l : list table_ref) : list ℚ :=
  compute_initial_distances_aux weights 0 l

def empty_partial_edit_distance_data (weights : table ℚ) (l₁ l₂ : list table_ref) : ed_partial :=
  ⟨ 0, l₁, compute_initial_distances weights l₂ ⟩

def triples {α : Type} (p : ed_partial) (l₂ : list α): list (ℚ × ℚ × α) :=
p.distances.zip ((list.cons p.prefix_length p.distances).zip l₂)

universe u

def minl {α : Type u} [inhabited α] [decidable_linear_order α] : list α → α
| [] := default α
| [a] := a
| (n :: rest) := min n (minl rest)

--FIXME explain me
meta def fold_fn (weights : table ℚ) (h : table_ref) (n : ℚ × list ℚ) : ℚ × ℚ × table_ref → ℚ × list ℚ
| (a, b, r) :=
  let m := if h = r then b else minl [
    /- deletion     -/ a + (get_weight weights r),
    /- substitution -/ b + max (get_weight weights r) (get_weight weights h),
    /- insertion    -/ n.2.head + (get_weight weights h)
  ] in
  (min m n.1, list.cons m n.2)

--FIXME explain me
meta def improve_bound_once (weights : table ℚ) (l r : list table_ref) (cur : ℚ) (p : ed_partial) : bound_progress ed_partial :=
  match p.suffix with
    | [] := exactly p.distances.ilast p
    | (h :: t) :=
      let new_prefix_length := p.prefix_length + /-(get_weight weights h)-/0 in
      let initial : ℚ × list ℚ := (new_prefix_length, [new_prefix_length]) in
      let new_distances : ℚ × list ℚ := (triples p r).foldl (fold_fn weights h) initial in
      at_least new_distances.1 ⟨ new_prefix_length, t, new_distances.2.reverse.drop 1 ⟩
  end

meta def improve_bound_over (weights : table ℚ) (l r : list table_ref) (m : ℚ) : bound_progress ed_partial → bound_progress ed_partial
| (exactly n p) := exactly n p
| (at_least n p) :=
  if n > m then
    at_least n p
  else
    improve_bound_over (improve_bound_once weights l r n p)

-- def l1 : list table_ref := [1,2,3,4].map table_ref.from_nat
-- def l2 : list table_ref := [1,1,2,3,4].map table_ref.from_nat

-- def weights : table ℚ := table.from_list [1,0,1,1,1,1]

-- def bp : bound_progress ed_partial := at_least 0 (empty_partial_edit_distance_data weights l1 l2)

-- #eval (ed_improve_bound_over weights l1 l2 10.0 bp).to_string

end tidy.rewrite_search.edit_distance

namespace tidy.rewrite_search.strategy.edit_distance

open tidy.rewrite_search.edit_distance

def MAX_ITERATIONS := 200

structure ed_config :=
(explain_thoughts : bool := ff)
(trace_weights    : bool := ff)

meta def calc_weights_fn := ed_config → table token → tactic (table ℚ)

structure search_state :=
  (weights : table ℚ)
def search_state.init : search_state := ⟨table.create⟩

meta def ed_init : search_state := search_state.init

variable (g : global_state search_state ed_partial)

meta def ed_init_bound (l r : vertex) : bound_progress ed_partial :=
  at_least 0 (empty_partial_edit_distance_data g.internal_strat_state.weights l.tokens r.tokens)

meta def ed_reweight (conf : ed_config) (fn : table token → tactic (table ℚ)) (g : global_state search_state ed_partial) : tactic (global_state search_state ed_partial) := do
  let g := g.reset_all_estimates ed_init_bound,
  weights ← fn g.tokens,
  if conf.trace_weights then
    let weight_pairs := (g.tokens.to_list.zip weights.to_list).map (
      λ p : token × ℚ, to_string format!"{p.1.str}:{p.2}"
    ) in
    tactic.trace format!"reweighted: {weight_pairs}"
  else
    tactic.skip,
  return $ g.mutate_strategy ⟨weights⟩

meta def ed_step (conf : ed_config) (refresh_freq : ℕ) (fn : table token → tactic (table ℚ)) (g : global_state search_state ed_partial) (itr : ℕ) : tactic (global_state search_state ed_partial × (@strategy_action search_state ed_partial)) :=
  if itr > MAX_ITERATIONS then
    return (g, strategy_action.abort "max iterations exceeded!")
  else if refresh_freq > 0 ∧ (itr % (refresh_freq + 1) = 0) then do
    if conf.explain_thoughts then tactic.trace "pause! refreshing weights..." else tactic.skip,
    return (g, strategy_action.refresh (ed_reweight conf fn))
  else
    match g.interesting_pairs with
    | [] :=               return (g, strategy_action.abort "all interesting pairs exhausted!")
    | (best_p :: rest) := return (g, strategy_action.examine best_p)
    end

meta def ed_improve_estimate_over (m : ℚ) (l r : vertex) (bnd : bound_progress ed_partial) : bound_progress ed_partial :=
  improve_bound_over g.internal_strat_state.weights l.tokens r.tokens m bnd

end tidy.rewrite_search.strategy.edit_distance

namespace tidy.rewrite_search.strategy

open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.strategy.edit_distance

meta def edit_distance_weighted (refresh_freq : ℕ) (fn : calc_weights_fn) (conf : ed_config := {}) : strategy search_state ed_partial :=
  ⟨ ed_init, ed_step conf refresh_freq (fn conf), ed_init_bound, ed_improve_estimate_over ⟩

meta def edit_distance (conf : ed_config := {}) : strategy search_state ed_partial :=
  edit_distance_weighted 0 (λ conf ts, return table.create) conf

end tidy.rewrite_search.strategy