import tidy.rewrite_search.core
import tidy.rewrite_search.metric.edit_distance

open tidy.rewrite_search
open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.metric.edit_distance

namespace tidy.rewrite_search.metric.edit_distance.weight.cm

def cm_of_side (l : list token) (s : side) : list ℚ :=
  let (tot, vec) := l.foldl (
    λ n : ℕ × list ℕ, λ t : token, let v := t.freq.get s in (n.1 + v, n.2.concat v)
  ) (0, []) in
  vec.map (λ n : ℕ, n / tot)

def compare_component (a b : ℚ) : ℚ := (abs (a - b)) * 4 + 1

def compare : list ℚ → list ℚ → list ℚ
  | (a :: l1) (b :: l2) := compare_component a b :: compare l1 l2
  | _ _ := []

meta def calculate_weights {α δ : Type} (g : search_state α ed_state ed_partial δ) : tactic (table ℚ) :=
  let tl := g.tokens.to_list in
  return $ table.from_list $ compare (cm_of_side tl side.L) (cm_of_side tl side.R)

end tidy.rewrite_search.metric.edit_distance.weight.cm

namespace tidy.rewrite_search.metric
open tidy.rewrite_search.metric.edit_distance.weight.cm

meta def weight.cm : ed_weight_constructor :=
  λ α δ, ⟨init_result.pure (), λ conf g, calculate_weights g⟩

end tidy.rewrite_search.metric