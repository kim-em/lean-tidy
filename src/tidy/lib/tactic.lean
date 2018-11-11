import .pretty_print

universe u

namespace tactic

meta def is_eq_after_binders : expr → bool
  | (expr.pi n bi d b) := is_eq_after_binders b
  | `(%%a = %%b)       := tt
  | _                  := ff

meta def is_iff_after_binders : expr → bool
  | (expr.pi n bi d b) := is_iff_after_binders b
  | `(%%a ↔ %%b)       := tt
  | _                  := ff

meta def is_eq_or_iff_after_binders : expr → bool
  | (expr.pi n bi d b) := is_eq_or_iff_after_binders b
  | `(%%a = %%b)       := tt
  | `(%%a ↔ %%b)       := tt
  | _                  := ff

meta def get_binder_types : expr → list expr
  | (expr.pi n bi d b) := d :: get_binder_types b
  | _                  := []

-- TODO is there any way to replace `type : expr` with an honest `α : Type`?
-- Maybe at least a `type : name`? In this case probably just need to read about
-- name resolution.
meta def assert_type (type : expr) (n : name) : tactic unit := do
  t ← infer_type (expr.const n []),
  guard $ t = type

meta def type_cast (α : Type u) [reflected α] (n : name) : tactic α :=
  eval_expr α (expr.const n [])

-- FIXME doesn't `unify` do exactly this??
meta def attempt_refl (lhs rhs : expr) : tactic expr :=
lock_tactic_state $
do
  gs ← get_goals,
  m ← to_expr ``(%%lhs = %%rhs) >>= mk_meta_var,
  set_goals [m],
  refl ← mk_const `eq.refl,
  apply_core refl {new_goals := new_goals.non_dep_only},
  instantiate_mvars m

meta def simp_expr (t : expr) (cfg : simp_config := {}) (discharger : tactic unit := failed) (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) : tactic (expr × expr) := do
  (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
  simplify s to_unfold t cfg `eq discharger

meta def dsimp_expr (t : expr) (cfg : dsimp_config := {}) (discharger : tactic unit := failed) (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) : tactic expr := do
  (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
  s.dsimplify to_unfold t cfg

meta def mk_app_aux : expr → expr → expr → tactic expr
 | f (expr.pi n binder_info.default d b) arg := do
   infer_type arg >>= unify d,
   return $ f arg
 | f (expr.pi n binder_info.inst_implicit d b) arg := do
   infer_type arg >>= unify d,
   return $ f arg -- TODO use typeclass inference?
 | f (expr.pi n _ d b) arg := do
   v ← mk_meta_var d,
   t ← whnf (b.instantiate_var v),
   mk_app_aux (f v) t arg
 | e _ _ := failed

-- TODO check if just the first will suffice
meta def mk_app' (f arg : expr) : tactic expr :=
lock_tactic_state $
do r ← to_expr ``(%%f %%arg) /- FIXME too expensive -/ <|> (do infer_type f >>= whnf >>= λ t, mk_app_aux f t arg),
   instantiate_mvars r

/--
Given an expression `e` and  list of expressions `F`, builds all applications of `e` to elements of `F`.
`mk_apps` returns a list of all pairs ``(`(%%e %%f), f)`` which typecheck, for `f` in the list `F`.
-/
meta def mk_apps (e : expr) (F : list expr) : tactic (list (expr × expr)) :=
do
   l ← F.mmap $ λ f, (do r ← try_core (mk_app' e f >>= λ m, return (m, f)), return r.to_list),
   return l.join

meta def if_not_done {α : Type} (t₁ : tactic α) (t₂ : tactic α) : tactic α := do
  ret ← t₁,
  (done >> return ret <|> t₂)

end tactic
