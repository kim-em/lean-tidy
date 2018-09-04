import tidy.rewrite_search.engine
import tidy.rewrite_search.strategy.edit_distance

import data.rat

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

def calc_cm (l : list token) (s : side) : list ℚ :=
  let (tot, vec) := l.foldl (
    λ n : ℕ × list ℕ, λ t : token, let v := t.freq s in (n.1 + v, n.2.concat v)
  ) (0, []) in
  vec.map (λ n : ℕ, n / tot)

def cm_diff : list ℚ → list ℚ → list ℚ
  | [] _ := []
  | _ [] := []
  | (a :: l1) (b :: l2) := ((abs ((a - b) * 4)) + 1) :: (cm_diff l1 l2)

def calc_cm_delta (tokens : table token) : list ℚ :=
  let tl := tokens.to_list in
  let cml := calc_cm tl side.L in
  let cmr := calc_cm tl side.R in
  cm_diff cml cmr

meta def cm_calc_weights (tokens : table token) : tactic (table ℚ) :=
  return $ table.from_list (calc_cm_delta tokens)

namespace tidy.rewrite_search.strategy

open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.strategy.edit_distance

meta def edit_distance_cm_weighted (refresh_freq : ℕ) : strategy search_state ed_partial :=
  ⟨ ed_init, ed_step refresh_freq cm_calc_weights, ed_init_bound, ed_improve_estimate_over ⟩

end tidy.rewrite_search.strategy