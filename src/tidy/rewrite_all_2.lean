import tidy.lib.mllist
import tidy.lib.pretty_print
import tidy.lib.tactic

universes u

open tactic
open mllist

meta def kabstract_no_new_goals (t e : expr) (md : transparency) : tactic expr :=
do gs ← get_goals,
   r ← kabstract t e md,
   ng ← num_goals,
   guard (ng = gs.length),
   return r

meta def kabstracter'
  (pattern : tactic (expr × expr × list expr))
  (lhs_replacer : list expr → tactic expr) :
  expr × list (expr × (list expr)) → tactic (expr × list (expr × (list expr)))
| p := do
  (t, L) ← pure p,
  (e, e_type, mvars) ← pattern,
  t' ← kabstract_no_new_goals t e semireducible,
  -- TODO use the discharger to clear remaining metavariables
  -- trace "kabstract:",
  -- trace t,
  -- trace e,
  -- trace mvars,
  -- mvars.mmap (λ m, infer_type m) >>= trace,
  -- trace t',
  guard t'.has_var,
  w ← mk_meta_var e_type,
  let t'' := t'.instantiate_var w,
  mvars' ← mvars.mmap instantiate_mvars,
  return (t'', (w, mvars') :: L) -- FIXME should there be a prime here??

meta def kabstracter
  (pattern : tactic (expr × expr × list expr))
  (lhs_replacer : list expr → tactic expr) (t : expr) : tactic (mllist tactic (expr × list (expr × list expr))) :=
mllist.fix (kabstracter' pattern lhs_replacer) (t, [])

meta def get_lhs : expr -> bool → list expr -> tactic (expr × expr × list expr)
| (expr.pi n bi d b) symm mvars :=
do v <- mk_meta_var d,
   b' <- whnf $ b.instantiate_var v,
   get_lhs b' symm (v :: mvars)
| `(%%a = %%b) symm mvars :=
  do let (a, b) := if symm then (b, a) else (a, b),
     ty ← infer_type a,
     return (a, ty, mvars)
| _ _ _ := failed

meta def replacer : expr -> bool → list expr -> tactic expr
| (expr.pi n bi d b) symm values := replacer b symm values
| `(%%a = %%b) symm values :=
  do let (a, b) := if symm then (b, a) else (a, b),
     return (a.instantiate_vars values)
| _ _ _ := failed

meta def mvars_to_var (e : expr) : expr :=
e.replace (λ e n, if e.is_meta_var then some (expr.var n) else none)

meta def do_substitutions
  (eq : expr) (symm : bool)
  (t_original : expr)
  (lhs rhs : list expr → tactic expr)
  (t_abstracted : expr)
  (rewrite_mvar : expr × list expr)
  (restore_mvars : list (expr × list expr)) : tactic (expr × tactic expr × list expr) :=
lock_tactic_state $
do -- We first restore all the "other" metavariables to their original values.
  --  trace "do_substitutions",
   restore_mvars.mmap (λ p, do l ← lhs p.2, unify p.1 l),
   t_restored ← instantiate_mvars t_abstracted,

   -- r' is the value of the remaining metavariable, after applying the lemma.
   r' ← rhs rewrite_mvar.2,

   guard (¬ r'.has_meta_var),
   -- We now begin constructing the `eq.rec` proof of equality. In fact, we don't construct it here,
   -- we just construct a tactic that can produce it on demand!
   let proof_tactic : tactic expr := do {
    -- r is the original value of the remaining metavariable
    r ← lhs rewrite_mvar.2,

    -- The lemma itself proves `r = r'`.
    let inner_proof := rewrite_mvar.2.reverse.foldl (λ f x : expr, f x) eq,
    inner_proof ← if symm then mk_eq_symm inner_proof else return inner_proof,
    -- trace "inner_proof:",
    -- trace inner_proof,

    -- Next we compute the motive.
    let t_with_var := mvars_to_var t_restored,
    n ← mk_fresh_name,
    -- trace "--",
    -- trace t_with_var,
    -- trace t_original,
    -- trace "r:",
    -- trace r,
    ty ← infer_type r,
    feq ← mk_const `eq,
    v ← mk_mvar,
    let C := expr.lam n binder_info.default ty (feq v t_original t_with_var),
    -- trace "motive:",
    -- trace C,

    -- ... and prepare the actual proof.
    refl ← mk_eq_refl t_original,
    proof ← to_expr ```(@eq.rec _ %%r %%C %%refl _ %%inner_proof),
    -- trace "proof:",
    -- trace proof,
    infer_type proof, -- this is a sanity check (perhaps we should be doing this earlier?)
    return proof
   },
   -- Finally we finish rewriting the expression
   unify rewrite_mvar.1 r',
   result ← instantiate_mvars t_restored,

   metas : list expr ← rewrite_mvar.2.mfilter (λ m, do r ← is_assigned m <|> return tt, return ¬ r),
   return (result, proof_tactic, metas)

meta def all_rewrites_core (t eq : expr) (symm : bool) : tactic (mllist tactic (expr × tactic expr × list expr)) :=
do ty ← infer_type eq,
  let matcher := get_lhs ty symm [],
  let lhs := replacer ty symm,
  let rhs := replacer ty ¬ symm,
  L ← kabstracter matcher lhs t,
  L.mfilter_map (λ p, do_substitutions eq symm t lhs rhs p.1 p.2.head p.2.tail)

meta structure rewrite_all_cfg extends rewrite_cfg :=
(try_simp   : bool := ff) -- TODO move the handling logic for me into rewrite_all_wrappers
(discharger : tactic unit := skip) -- FIXME this is ignored for now
(simplifier : expr → tactic (expr × expr) := λ e, failed) -- FIXME get rid of this?

meta def all_rewrites_lazy (r : expr × bool) (t : expr) (cfg : rewrite_all_cfg := {}) : tactic (mllist tactic (expr × (tactic expr))) :=
do
   L ← all_rewrites_core t r.1 r.2,
   L.filter_map (λ p, if p.2.2 = [] then some (p.1, p.2.1) else none)

meta def all_rewrites (r : expr × bool) (t : expr) (cfg : rewrite_all_cfg := {}): tactic (list (expr × expr)) :=
do L ← all_rewrites_lazy r t cfg,
   L ← L.mmap (λ p, do r ← p.2, return (p.1, r)),
   L.force

