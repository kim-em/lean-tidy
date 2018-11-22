import tactic.iconfig
import .core

structure tidy.rewrite_search.collect_config :=
(suggest         : list name := [])
(inflate_rws     : bool := ff)
(help_me         : bool := ff)

section

iconfig_mk rewrite_search

iconfig_add_struct rewrite_search tidy.rewrite_search.config
iconfig_add_struct rewrite_search tidy.rewrite_search.collect_config

open interactive lean.parser

-- TODO nicer default specification
iconfig_add rewrite_search [
  strategy : lpexpr,
  metric   : lpexpr,
  tracer   : lpexpr,
]

end

open tactic

meta def mk_mvars (type : expr) : ℕ → tactic (list expr)
| 0 := return []
| (n + 1) := do
  m ← tactic.mk_meta_var type,
  rest ← mk_mvars n,
  return (m :: rest)

meta def eval_pexpr (α : Type) [reflected α] (p : pexpr) : tactic α :=
  to_expr p >>= eval_expr α

meta def munify_app (n : name) (l : list expr) (t : tactic expr) : tactic expr := do
  m ← mk_app n l >>= mk_meta_var,
  t >>= unify m,
  return m

meta def expr.namespace_app {elab : bool} (ns : name) : expr elab → expr elab
| (expr.const n l) := expr.const (ns.append n) l
| (expr.local_const n _ _ _) := expr.const (ns.append n) []
| (expr.app f a)   := expr.app (f.namespace_app) a
| (expr.lam n bi t v) := expr.lam n bi t v.namespace_app
| e := e

namespace tidy.rewrite_search

meta structure sig :=
(α β γ δ : Type)

meta def sig_fn := Π (α β γ δ : Type), Type

meta structure packet (fn : sig_fn) :=
(sig : sig)
(v : fn sig.α sig.β sig.γ sig.δ)

meta structure module_stack :=
(s : sig)
(st : strategy s.α s.β s.γ s.δ)
(mt : metric s.α s.β s.γ s.δ)
(tr : tracer s.α s.β s.γ s.δ)

meta def instantiate_modules (st mt tr : pexpr) : tactic module_stack := do
  ulift.up e ← tactic.up $ (do
    let ns := [`strategy, `metric, `tracer].map $ λ n, `tidy.rewrite_search ++ n,

    [st, mt, tr] ← pure $ ns.zip_with expr.namespace_app [st, mt, tr],
    [st, mt, tr] ← [st, mt, tr].mmap $ eval_pexpr $ tactic expr,
    [α, β, γ, δ] ← mk_mvars `(Type) 4,

    st ← munify_app `tidy.rewrite_search.strategy [α, β, γ, δ] st,
    mt ← munify_app `tidy.rewrite_search.metric   [α, β, γ, δ] mt,
    tr ← munify_app `tidy.rewrite_search.tracer   [α, β, γ, δ] tr,

    [α, β, γ, δ, st, mt, tr] ← [α, β, γ, δ, st, mt, tr].mmap instantiate_mvars,

    s ← mk_app `tidy.rewrite_search.sig.mk [α, β, γ, δ],
    [s, st, mt, tr] ← pure $ [s, st, mt, tr].map pexpr.of_expr,
    to_expr $ ``(tidy.rewrite_search.module_stack.mk) s st mt tr
  ),
  eval_expr module_stack e

meta def generic_constructor_args (num_vars : ℕ) (fn : name) (e : list expr) : tactic expr := do
  fn ← resolve_name fn,
  ms ← mk_mvars `(Type) num_vars,
  tactic.to_expr $ ((e ++ ms).map pexpr.of_expr).foldl (λ h e : pexpr, h.app e) fn

meta def generic_constructor_arg (num_vars : ℕ) (fn : name) (e : expr) : tactic expr :=
  generic_constructor_args num_vars fn [e]

meta def generic_constructor (num_vars : ℕ) (fn : name) : tactic expr :=
  generic_constructor_args num_vars fn []

meta def strategy.generic : name → tactic expr := generic_constructor 3
meta def strategy.generic_arg : name → expr → tactic expr := generic_constructor_arg 3
meta def strategy.generic_args : name → list expr → tactic expr := generic_constructor_args 3
meta def metric.generic : name → tactic expr := generic_constructor 2
meta def metric.generic_arg : name → expr → tactic expr := generic_constructor_arg 2
meta def metric.generic_args : name → list expr → tactic expr := generic_constructor_args 2
meta def tracer.generic : name → tactic expr := generic_constructor 3
meta def tracer.generic_arg : name → expr → tactic expr := generic_constructor_arg 3
meta def tracer.generic_args : name → list expr → tactic expr := generic_constructor_args 3

end tidy.rewrite_search
