import data.list
import data.option

open tactic

meta def mk_app_aux : expr → expr → expr → tactic expr
 | f (expr.pi n binder_info.default d b) arg := do
   infer_type arg >>= unify d,
   return $ f arg
 | f (expr.pi n _ d b) arg := do
   v ← mk_meta_var d,
   t ← whnf (b.instantiate_var v),
   mk_app_aux (f v) t arg
 | e _ _ := failed

meta def mk_app' (f arg : expr) : tactic expr :=
do t ← infer_type f >>= whnf,
   mk_app_aux f t arg

meta def mk_apps (e : expr) (F : list expr) : tactic (list expr) :=
-- lock_tactic_state $
do l ← F.mmap $ λ f, (do r ← try_core (mk_app' e f), return r.to_list), return l.join
