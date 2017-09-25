-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

meta def applicable_attribute : user_attribute := {
  name := `applicable,
  descr := "A lemma that should be applied to a goal whenever possible."
}
meta def semiapplicable_attribute : user_attribute := {
  name := `semiapplicable,
  descr := "A lemma that should be applied to a goal whenever possible, as long as it create no new goals."
}

run_cmd attribute.register `applicable_attribute

/- Try to apply one of the given lemmas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic name
| []      := failed
| (c::cs) := (mk_const c >>= fapply >> pure c) <|> any_apply cs

/- Try to apply one of the given lemmas, fulfilling all new goals using existing hypotheses. It succeeds if one of them succeeds. -/
meta def any_apply_no_new_goals : list name → tactic name
| []      := failed
| (c::cs) := (do n ← num_goals,
                 t ← mk_const c,
                 r ← seq (fapply t) assumption,
                 n' ← num_goals,
                 guard (n = n + 1),
                 pure c) <|> any_apply cs

meta def applicable : tactic name :=
do cs ← attribute.get_instances `applicable,
   (any_apply cs) <|> fail "no @[applicable] lemmas could be applied"
meta def semiapplicable : tactic name :=
do cs ← attribute.get_instances `semiapplicable,
   (any_apply_no_new_goals cs) <|> fail "no @[semiapplicable] lemmas could be applied"

attribute [applicable] funext
attribute [applicable] subtype.eq