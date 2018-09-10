import tidy.lock_tactic_state

namespace tactic

-- FIXME doesn't `unify` do exactly this??
meta def attempt_refl (lhs rhs : expr) : tactic expr :=
lock_tactic_state $
do
  gs ← get_goals,
  m ← to_expr ``(%%lhs = %%rhs) >>= mk_meta_var,
  set_goals [m],
  refl ← mk_const `eq.refl,
  tactic.apply_core refl {new_goals := new_goals.non_dep_only},
  instantiate_mvars m

-- TODO Am I even good? Do I work? Do I slow us down too much?
meta def simp_expr (t : expr) (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) (cfg : simp_config := {}) (discharger : tactic unit := failed) : tactic (expr × expr) := do
  (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
  simplify s to_unfold t cfg `eq discharger

meta def dsimp_expr (t : expr) (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) (cfg : dsimp_config := {}) (discharger : tactic unit := failed) : tactic expr := do
  (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
  s.dsimplify to_unfold t cfg

end tactic