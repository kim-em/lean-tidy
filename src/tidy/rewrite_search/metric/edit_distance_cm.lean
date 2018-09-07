import tidy.rewrite_search.core
import tidy.rewrite_search.metric.edit_distance

open tidy.rewrite_search
open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.metric.edit_distance

namespace tidy.rewrite_search.metric.edit_distance.weight.cm

def cm_of_side (l : list token) (s : side) : list ℚ :=
  let (tot, vec) := l.foldl (
    λ n : ℕ × list ℕ, λ t : token, let v := t.freq s in (n.1 + v, n.2.concat v)
  ) (0, []) in
  vec.map (λ n : ℕ, n / tot)

def compare_component (a b : ℚ) : ℚ := (abs (a - b)) * 4 + 1

def compare : list ℚ → list ℚ → list ℚ
  | (a :: l1) (b :: l2) := compare_component a b :: compare l1 l2
  | _ _ := []

def calculate_weights (tokens : table token) : list ℚ :=
  let tl := tokens.to_list in
  compare (cm_of_side tl side.L) (cm_of_side tl side.R)

end tidy.rewrite_search.metric.edit_distance.weight.cm

namespace tidy.rewrite_search.metric
open tidy.rewrite_search.metric.edit_distance.weight.cm

meta def weight.cm (_ : ed_config) (tokens : table token) : tactic (table ℚ) :=
  return $ table.from_list (calculate_weights tokens)

end tidy.rewrite_search.metric