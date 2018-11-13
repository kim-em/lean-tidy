import libk
import tidy.lib.num

import tidy.rewrite_search.core
import tidy.rewrite_search.metric.edit_distance

open tidy.rewrite_search
open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.metric.edit_distance

namespace tidy.rewrite_search.metric.edit_distance.weight.svm

variables {α δ : Type} (g : search_state α ed_state ed_partial δ)

meta def init : tactic (init_result unit) :=
  if k.is_available then
    init_result.pure ()
  else
    init_result.fail "SVM weights are only available through the \"klean\" fork. If you use elan, simply change \"lean_version\" in your \"leanpkg.toml\" to \"khoek/klean:3.4.4\" (and restart the lean server) to gain access to libSVM. Otherwise, you can fetch klean yourself from 'https://github.com/khoek/klean/releases/tag/v3.4.4' and just install it as normal.\n\nIt may take a few moments for your editor to download the new lean version after you restart lean."

meta def fill_token_vector_aux {dim : ℕ} : list table_ref → ℕ → array dim ℕ → array dim ℕ
| [] idx vec := vec
| (t :: rest) idx vec :=
  dite (dim = 0) (λ _, vec) (λ hnz,
    let f : fin dim := fin.with_max t dim hnz in
    fill_token_vector_aux rest (idx + 1) $ vec.write f $ (vec.read f) + 1
  )

meta def fill_token_vector {dim : ℕ} (l : list table_ref) (buff : array dim ℕ) : array dim ℕ :=
  fill_token_vector_aux l 0 buff

meta def build_token_vector {dim : ℕ} (tokens : list table_ref) : array dim ℕ :=
  fill_token_vector tokens $ mk_array dim 0

meta def build_vector_lists_aux {dim : ℕ} (vertices : table vertex) : table_ref → sided_pair (list (array dim ℕ))
| ref :=
  match vertices.at_ref ref with
  | none := ⟨[], []⟩
  | some v :=
    let rest := build_vector_lists_aux ref.next in
    rest.set v.s $ (build_token_vector v.tokens :: rest.get v.s)
  end

meta def build_vector_lists (dim : ℕ) (vertices : table vertex) : sided_pair (list (array dim ℕ)) :=
  build_vector_lists_aux vertices table_ref.first

meta def calculate_weights : tactic (table dnum) := do
  let dim := g.tokens.length,
  let ⟨lvs, rvs⟩ := build_vector_lists dim g.vertices,
  let (n, b) := k.find_separating_hyperplane lvs rvs,
  return $ table.from_map_array n $ λ c, 1 + rat.mk (1 * abs c) 1000

end tidy.rewrite_search.metric.edit_distance.weight.svm

namespace tidy.rewrite_search.metric
open tidy.rewrite_search.metric.edit_distance.weight.svm

meta def weight.svm : ed_weight_constructor :=
  λ α δ, ⟨tidy.rewrite_search.metric.edit_distance.weight.svm.init, λ conf g, calculate_weights g⟩

end tidy.rewrite_search.metric
