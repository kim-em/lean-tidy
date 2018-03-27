open tactic
meta def simplify_proof {α} [has_to_format α] (tac : tactic α) : tactic α :=
λ s,
  let tac1 : tactic (α × expr) := do
    a ← tac,
    r ← result,
    lems ← simp_lemmas.mk_default,
    dr ← (lems.dsimplify [] r <|> pure r),
    pure (a, dr) in
match tac1 s with
| result.success (a, r) s' := (result >>= unify r >> pure a) s'
| result.exception msg e s' := result.exception msg e s'
end