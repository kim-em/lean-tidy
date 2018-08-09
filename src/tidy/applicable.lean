-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .pempty

open tactic

meta def applicable_attribute : user_attribute := {
  name := `applicable,
  descr := "A lemma that should be applied to a goal whenever possible."
}

run_cmd attribute.register `applicable_attribute

/- Try to apply one of the given lemmas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic name
| []      := failed
| (c::cs) := (mk_const c >>= apply >> pure c) <|> any_apply cs

/- Try to apply any lemma marked with the attribute @[applicable] -/
meta def applicable : tactic name :=
do cs ← attribute.get_instances `applicable,
   (any_apply cs) <|> fail "no @[applicable] lemmas could be applied"

meta def get_applicable_lemmas : tactic unit :=
do cs ← attribute.get_instances `applicable,
   tactic.trace (list.foldl (λ s n, name.to_string n ++ ", " ++ s) "" cs)

meta def semiapplicable_attribute : user_attribute := {
  name := `semiapplicable,
  descr := "A lemma that should be applied to a goal whenever possible, as long as it create no new goals."
}

run_cmd attribute.register `semiapplicable_attribute

/- Try to apply one of the given lemmas, fulfilling all new goals using existing hypotheses. It succeeds if one of them succeeds. -/
meta def any_apply_no_new_goals : list name → tactic name
| []      := failed
| (c::cs) := (do n ← num_goals,
                 t ← mk_const c,
                 r ← seq (apply t >> skip) assumption,
                 n' ← num_goals,
                 guard (n = n' + 1),
                 pure c) <|> any_apply_no_new_goals cs

/- Try to apply any lemma marked with the attribute @[semiapplicable], as long as all hypotheses of that lemma can be satisfied immediately from hypotheses. -/
meta def semiapplicable : tactic name :=
do cs ← attribute.get_instances `semiapplicable,
   (any_apply_no_new_goals cs) <|> fail "no @[semiapplicable] lemmas could be applied"

attribute [applicable] subsingleton.elim

attribute [applicable] funext
attribute [applicable] set.ext   -- Order matters here: putting the attribute on set.ext after funext makes applicable prefer set.ext
attribute [applicable] propext
attribute [applicable] subtype.eq

universes u₁ u₂

@[applicable] definition empty_exfalso (x : false) : empty := begin exfalso, trivial end
@[applicable] definition pempty_exfalso (x : false) : pempty := begin exfalso, trivial end

@[applicable] lemma punit.ext (a b : punit.{u₁}): a = b := by induction a; induction b; refl
@[applicable] lemma ulift.ext {α : Type u₁} (X Y : ulift.{u₂} α) (w : X.down = Y.down) : X = Y :=
begin
  induction X, induction Y, dsimp at w, rw w,
end
@[applicable] lemma sigma.ext {α : Type u₁} (Z : α → Type u₂) (X Y : Σ a : α, Z a) (w1 : X.1 = Y.1) (w2 : @eq.rec_on _ X.1 _ _ w1 X.2 = Y.2) : X = Y :=
begin
  induction X, induction Y, dsimp at w1, dsimp at w2, induction w1, induction w2, refl,
end
@[applicable] lemma pair.ext {α : Type u₁} {β : Type u₂} {X Y : α × β} (p1 : X.1 = Y.1) (p2 : X.2 = Y.2) : X = Y := 
begin
  induction X, induction Y, dsimp at *, rw p1, rw p2,
end

-- TODO should `apply_instance` be in tidy? If so, these shouldn't be needed.
@[applicable] definition decidable_true  : decidable true  := is_true  dec_trivial
@[applicable] definition decidable_false : decidable false := is_false dec_trivial

attribute [applicable] quotient.mk quotient.sound
attribute [semiapplicable] eqv_gen.rel

attribute [semiapplicable] Exists.intro
