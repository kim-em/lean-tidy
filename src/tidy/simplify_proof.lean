open tactic
meta def simplify_proof (tac : tactic unit) : tactic unit :=
λ s,
  let tac1 : tactic expr := do
    tac,
    r ← result,
    lems ← simp_lemmas.mk_default,
    lems.dsimplify [] r in
match tac1 s with
| result.success r s' := (result >>= unify r) s
| result.exception msg e s' := result.exception msg e s'
end