import tidy.rewrite_search.core

-- The trivial metric: I just report that every vertex is distance zero from every other.

open tidy.rewrite_search

namespace tidy.rewrite_search.metric.trivial

variables {α δ : Type} (g : search_state α unit unit δ)

meta def trivial_init : unit := ()
meta def trivial_update (itr : ℕ) : tactic (search_state α unit unit δ) := return g
meta def trivial_init_bound (_ : search_state α unit unit δ) (l r : vertex) : bound_progress unit := bound_progress.exactly 0 ()
meta def trivial_improve_estimate_over (_ : search_state α unit unit δ) (m : ℚ) (l r : vertex) (bnd : bound_progress unit) : bound_progress unit := bound_progress.exactly 0 ()

end tidy.rewrite_search.metric.trivial

namespace tidy.rewrite_search.metric

open tidy.rewrite_search.metric.trivial

meta def trivial : metric_constructor unit unit :=
  λ α δ, ⟨ trivial_init, trivial_update, trivial_init_bound, trivial_improve_estimate_over ⟩

end tidy.rewrite_search.metric