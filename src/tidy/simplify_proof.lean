-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mario Carneiro, Scott Morrison

open tactic
meta def simplify_proof {α} (tac : tactic α) : tactic α :=
λ s,
  let tac1 : tactic (α × (list expr) × expr) := do
    a ← tac,
    r ← result,
    lems ← simp_lemmas.mk_default,
    dr ← (lems.dsimplify [] r <|> pure r),
    g ← get_goals,
    pure (a, g, dr) in
match tac1 s with
| result.success (a, g, r) s' := match (result >>= unify r >> set_goals g >> pp r >>= trace >> pure a) s with
  | result.success a s'' := result.success a s''
  | result.exception msg _ _ := result.success a s' -- if unification fails for some reason, just discard the simplification
  end
| result.exception msg e s' := result.exception msg e s'
end