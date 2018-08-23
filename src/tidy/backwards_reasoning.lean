-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .pempty
import .recover

open tactic

meta def back_attribute : user_attribute := {
  name := `back,
  descr := "A lemma that should be applied to a goal whenever possible; use `backwards_reasoning` to automatically `apply` all lemmas tagged `[back]`."
}

run_cmd attribute.register `back_attribute

/-- Try to apply one of the given lemmas; it succeeds as soon as one of them succeeds. -/
meta def any_apply : list name → tactic name
| []      := failed
| (c::cs) := (mk_const c >>= apply >> pure c) <|> any_apply cs

meta def back'_attribute : user_attribute := {
  name := `back',
  descr := "A lemma that should be applied to a goal whenever possible, as long as all arguments to the lemma by be fulfilled from existing hypotheses; use `backwards_reasoning` to automatically apply all lemmas tagged `[back']`."
}

run_cmd attribute.register `back'_attribute
meta def seq (tac1 : tactic unit) (tac2 : tactic unit) : tactic unit :=
do g::gs ← get_goals,
   set_goals [g],
   tac1, all_goals tac2,
   gs' ← get_goals,
   set_goals (gs' ++ gs)

/-- Try to apply one of the given lemmas, fulfilling all new goals using existing hypotheses. It succeeds if one of them succeeds. -/
meta def any_apply_no_new_goals : list name → tactic name
| []      := failed
| (c::cs) := (do g::gs ← get_goals,
                 set_goals [g],
                 t ← mk_const c,
                 r ← apply t,
                 all_goals solve_by_elim,
                 a ← r.mmap (λ p, do e ← instantiate_mvars p.2, return e.metavariables.length),
                 guard (a.all (λ n, n = 0)),
                 gs' ← get_goals,
                 set_goals (gs' ++ gs),
                 pure c) <|> any_apply_no_new_goals cs

/-- Try to apply any lemma marked with the attributes `@[back]` or `@[back']`. -/
meta def backwards_reasoning : tactic string :=
do cs ← attribute.get_instances `back',
   r ← try_core (any_apply_no_new_goals cs),
   match r with 
   | (some n) := return ("apply " ++ n.to_string ++ " ; solve_by_elim")
   | none     :=  do 
                    cs ← attribute.get_instances `back,
                    n ← any_apply cs <|> fail "no @[back] or @[back'] lemmas could be applied",
                    return ("apply " ++ n.to_string)
   end

attribute [extensionality] subtype.eq

-- TODO get from subsingleton.elim?
-- @[extensionality] lemma punit_ext (a b : punit.{u₁}) : a = b := begin induction a, induction b, refl end
-- @[extensionality] lemma sigma_ext {α : Type u₁} (Z : α → Type u₂) (X Y : Σ a : α, Z a) (w₁ : X.1 = Y.1) (w₂ : @eq.rec_on _ X.1 _ _ w₁ X.2 = Y.2) : X = Y :=
-- begin
--   induction X, induction Y, dsimp at w₁, dsimp at w₂, induction w₁, induction w₂, refl,
-- end

-- TODO should `apply_instance` be in tidy? If so, these shouldn't be needed.
@[back] definition decidable_true  : decidable true  := is_true  dec_trivial
@[back] definition decidable_false : decidable false := is_false dec_trivial

attribute [back] quotient.mk quotient.sound

attribute [back] eqv_gen.rel
attribute [back'] Exists.intro
