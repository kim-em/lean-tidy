import data.list
import data.option
import .lock_tactic_state

open tactic

meta def mk_app_aux : expr → expr → expr → tactic expr
 | f (expr.pi n binder_info.default d b) arg := do
   infer_type arg >>= unify d,
   return $ f arg
 | f (expr.pi n binder_info.inst_implicit d b) arg := do
   infer_type arg >>= unify d,
   return $ f arg -- TODO use typeclass inference?
  --  v ← mk_instance d,
  --  t ← whnf (b.instantiate_var v),
  --  mk_app_aux (f v) t arg   
 | f (expr.pi n _ d b) arg := do
   v ← mk_meta_var d,
   t ← whnf (b.instantiate_var v),
   mk_app_aux (f v) t arg
 | e _ _ := failed

-- TODO check if just the first will suffice
meta def mk_app' (f arg : expr) : tactic expr :=
do r ← to_expr ``(%%f %%arg) <|> (do infer_type f >>= whnf >>= λ t, mk_app_aux f t arg),
   instantiate_mvars r

/--
Given an expression `e` and  list of expressions `F`, builds all applications of `e` to elements of `F`. 
`mk_apps` returns a list of all pairs ``(`(%%e %%f), f)`` which typecheck, for `f` in the list `F`.
-/
meta def mk_apps (e : expr) (F : list expr) : tactic (list (expr × expr)) :=
lock_tactic_state $
do 
   l ← F.mmap $ λ f, (do r ← try_core (mk_app' e f >>= λ m, return (m, f)), return r.to_list), 
   return l.join
