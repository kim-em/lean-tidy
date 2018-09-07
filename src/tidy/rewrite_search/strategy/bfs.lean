import tidy.rewrite_search.core

open tidy.rewrite_search

namespace tidy.rewrite_search.strategy.bfs

structure bfs_config :=
(max_depth : ℕ := 50)

structure bfs_state :=
(curr_depth : ℕ)
(queue      : list (option table_ref))

variables {β γ δ : Type} (conf : bfs_config) (g : search_state bfs_state β γ δ)

meta def bfs_init : bfs_state := ⟨ 1, [] ⟩

meta def bfs_startup (m : metric bfs_state β γ δ) (l r : vertex) : tactic (search_state bfs_state β γ δ) :=
  return $ g.mutate_strat ⟨ 1, [l.id, r.id, none] ⟩

meta def bfs_step (g : search_state bfs_state β γ δ) (_ : metric bfs_state β γ δ) (_: ℕ) : tactic (search_state bfs_state β γ δ × status) := do
  let state := g.strat_state,
  if state.curr_depth > conf.max_depth then
    return (g, status.abort "max bfs depth reached!")
  else match state.queue with
  | [] := return (g, status.abort "all vertices exhausted!")
  | (none :: rest) := do
    return (g.mutate_strat {state with queue := rest.concat none, curr_depth := state.curr_depth + 1}, status.repeat)
  | (some v :: rest) := do
    v ← g.vertices.get v,
    (g, adjs) ← g.visit_vertex v,
    let adjs := adjs.filter $ λ u, ¬u.visited,
    return (g.mutate_strat {state with queue := rest.append $ adjs.map $ λ u, some u.id}, status.continue)
  end

end tidy.rewrite_search.strategy.bfs

namespace tidy.rewrite_search.strategy

open tidy.rewrite_search.strategy.bfs

meta def bfs (conf : bfs_config := {}) : strategy_constructor bfs_state := 
λ β γ δ, strategy.mk bfs_init (@bfs_startup β γ δ) (@bfs_step β γ δ conf)

end tidy.rewrite_search.strategy