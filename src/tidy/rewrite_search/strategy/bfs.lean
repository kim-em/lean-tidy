import tactic.iconfig
import tidy.rewrite_search.core
import tidy.rewrite_search.module

open tidy.rewrite_search

namespace tidy.rewrite_search.strategy.bfs

structure bfs_config :=
(max_depth : ℕ := 50)

structure bfs_state :=
(conf       : bfs_config)
(curr_depth : ℕ)
(queue      : list (option table_ref))

variables {β γ δ : Type} (g : search_state bfs_state β γ δ)

meta def bfs_init : tactic (init_result bfs_state) := init_result.pure ⟨{}, 1, []⟩

meta def bfs_startup (cfg : iconfig.result) (g : search_state bfs_state β γ δ) (m : metric bfs_state β γ δ) (l r : vertex) : tactic (search_state bfs_state β γ δ) := do
  cfg ← cfg.struct `tidy.rewrite_search.strategy.bfs.bfs_config bfs_config,
  return $ g.mutate_strat ⟨cfg, 1, [l.id, r.id, none]⟩

meta def bfs_step (g : search_state bfs_state β γ δ) (_ : metric bfs_state β γ δ) (_: ℕ) : tactic (search_state bfs_state β γ δ × status) := do
  let state := g.strat_state,
  if state.curr_depth > g.strat_state.conf.max_depth then
    return (g, status.abort "max bfs depth reached!")
  else match state.queue with
  | [] := return (g, status.abort "all vertices exhausted!")
  | (none :: rest) := do
    return (g.mutate_strat {state with queue := rest.concat none, curr_depth := state.curr_depth + 1}, status.repeat)
  | (some v :: rest) := do
    v ← g.vertices.get v,
    (g, it) ← g.visit_vertex v,
    (g, it, adjs) ← it.exhaust g,
    let adjs := adjs.filter $ λ u, ¬u.1.visited,
    return (g.mutate_strat {state with queue := rest.append $ adjs.map $ λ u, some u.1.id}, status.continue)
  end

end tidy.rewrite_search.strategy.bfs

namespace tidy.rewrite_search.strategy

open tidy.rewrite_search.strategy.bfs

meta def bfs_const (conf : iconfig.result) := λ β γ δ, strategy.mk bfs_init (@bfs_startup β γ δ conf) (@bfs_step β γ δ)

meta def bfs (conf : iconfig.result := iconfig.empty_result) : tactic expr :=
  generic_arg `tidy.rewrite_search.strategy.bfs_const `(conf)

section

iconfig_mk bfs
iconfig_add_struct bfs tidy.rewrite_search.strategy.bfs.bfs_config

meta def bfs_cfg (_ : name) (cfg : iconfig bfs) : cfgtactic unit := do
  cfg ← iconfig.read cfg,
  e ← tactic.to_expr $ ``(bfs) $ pexpr.of_expr `(cfg),
  iconfig.publish `strategy $ cfgopt.value.pexpr $ pexpr.of_expr e

iconfig_add rewrite_search [ strategy.bfs : custom bfs_cfg ]

end

end tidy.rewrite_search.strategy
