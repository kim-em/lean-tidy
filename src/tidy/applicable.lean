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
run_cmd attribute.register `semiapplicable_attribute

/- Try to apply one of the given lemmas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic name
| []      := failed
| (c::cs) := (mk_const c >>= fapply >> pure c) <|> any_apply cs

/- Try to apply one of the given lemmas, fulfilling all new goals using existing hypotheses. It succeeds if one of them succeeds. -/
meta def any_apply_no_new_goals : list name → tactic name
| []      := failed
| (c::cs) := (do n ← num_goals,
                 t ← mk_const c,
                 r ← seq (fapply t >> skip) assumption,
                 n' ← num_goals,
                 guard (n = n' + 1),
                 pure c) <|> any_apply_no_new_goals cs

meta def applicable : tactic name :=
do cs ← attribute.get_instances `applicable,
   (any_apply cs) <|> fail "no @[applicable] lemmas could be applied"

-- PROJECT semiapplicable could use safe tactics, such as `terminal_goal >> solve_by_elim`
meta def semiapplicable : tactic name :=
do cs ← attribute.get_instances `semiapplicable,
   (any_apply_no_new_goals cs) <|> fail "no @[semiapplicable] lemmas could be applied"

attribute [applicable] funext
attribute [applicable] propext
attribute [applicable] subtype.eq
attribute [applicable] proof_irrel

universes u₁ u₂

@[applicable] lemma punits_equal (a b : punit.{u₁}): a = b := by induction a; induction b; refl
@[applicable] lemma ulifts_equal {α : Type u₁} (X Y : ulift.{u₂} α) (w : X.down = Y.down) : X = Y :=
begin
  induction X,
  induction Y,
  dsimp at w,
  rw w,
end
@[applicable] lemma sigmas_equal {α : Type u₁} (Z : α → Type u₂) (X Y : Σ a : α, Z a) (w1 : X.1 = Y.1) (w2 : @eq.rec_on _ X.1 _ _ w1 X.2 = Y.2) : X = Y :=
begin
  induction X,
  induction Y,
  dsimp at w1,
  dsimp at w2,
  induction w1,
  induction w2,
  refl,
end
@[applicable] lemma pairs_equal {α : Type u₁} {β : Type u₁} {X Y : α × β} (p1 : X.1 = Y.1) (p2 : X.2 = Y.2) : X = Y := 
begin
  induction X, induction Y, dsimp at *, rw p1, rw p2,
end

