-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tactic.basic
import tactic.ext

open tactic

meta def back_attribute : user_attribute := {
  name := `back,
  descr := "A lemma that should be applied to a goal whenever possible; use `backwards_reasoning` to automatically `apply` all lemmas tagged `[back]`."
}

run_cmd attribute.register ``back_attribute

/-- Try to apply the given lemma, solving new terminal goals by solve_by_elim if possible. -/
meta def apply_using_solve_by_elim (c : name) : tactic unit :=
focus1 $ do
  t ← mk_const c,
  r ← apply t,
  try (any_goals (terminal_goal >> solve_by_elim))

meta def elim_attribute : user_attribute := {
  name := `elim,
  descr := "A lemma that should be applied to a goal whenever possible, as long as all arguments to the lemma by be fulfilled from existing hypotheses; use `backwards_reasoning` to automatically apply all lemmas tagged `[elim]`."
}

run_cmd attribute.register ``elim_attribute

/-- Try to apply the given lemma, fulfilling all new goals using existing hypotheses. -/
meta def apply_no_new_goals (c : name) : tactic unit :=
focus1 $ do
  t ← mk_const c,
  r ← apply t,
  all_goals solve_by_elim,
  a ← r.mmap (λ p, do e ← instantiate_mvars p.2, return e.list_meta_vars.length),
  guard (a.all (λ n, n = 0))

/-- Try to apply one of the given lemmas; it succeeds as soon as one of them succeeds. -/
meta def any_apply_with (f : name → tactic unit) : list name → tactic name
| []      := failed
| (c::cs) := (f c >> pure c) <|> any_apply_with cs

/-- Try to apply any lemma marked with the attributes `@[back]` or `@[elim]`. -/
meta def backwards_reasoning : tactic string :=
(attribute.get_instances `elim >>= any_apply_with apply_no_new_goals >>=
  λ n, return ("apply " ++ n.to_string ++ " ; solve_by_elim")) <|>
(attribute.get_instances `back >>= any_apply_with apply_using_solve_by_elim >>=
  λ n, return ("apply " ++ n.to_string)) <|>
fail "no @[back] or @[back'] lemmas could be applied"

attribute [extensionality] subtype.eq

-- TODO should `apply_instance` be in tidy? If so, these shouldn't be needed.
@[back] definition decidable_true  : decidable true  := is_true  dec_trivial
@[back] definition decidable_false : decidable false := is_false dec_trivial

attribute [back] quotient.mk quotient.sound

attribute [back] eqv_gen.rel
attribute [elim] Exists.intro
