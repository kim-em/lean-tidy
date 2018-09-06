import tidy.rewrite_search.engine
import tidy.rewrite_search.metric.edit_distance

import data.rat

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.metric.edit_distance

def cm_of_side (l : list token) (s : side) : list ℚ :=
  let (tot, vec) := l.foldl (
    λ n : ℕ × list ℕ, λ t : token, let v := t.freq s in (n.1 + v, n.2.concat v)
  ) (0, []) in
  vec.map (λ n : ℕ, n / tot)

def cm_compare : list ℚ → list ℚ → list ℚ
  | (a :: l1) (b :: l2) := ((abs ((a - b) * 4)) + 1) :: (cm_compare l1 l2)
  | _ _ := []

def cm_calculate_weights (tokens : table token) : list ℚ :=
  let tl := tokens.to_list in
  cm_compare (cm_of_side tl side.L) (cm_of_side tl side.R)

meta def cm_calc_weights (_ : ed_config) (tokens : table token) : tactic (table ℚ) :=
  return $ table.from_list (cm_calculate_weights tokens)

namespace tidy.rewrite_search.metric

meta def edit_distance_cm_weighted (refresh_freq : ℕ) (conf : ed_config := {}) : metric_constructor ed_state ed_partial :=
  edit_distance_weighted refresh_freq cm_calc_weights conf

end tidy.rewrite_search.metric