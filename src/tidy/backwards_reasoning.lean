-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .pempty

open tactic

meta def backwards_attribute : user_attribute := {
  name := `backwards,
  descr := "A lemma that should be applied to a goal whenever possible; use `backwards_reasoning` to automatically `apply` all lemmas tagged `backwards`."
}

run_cmd attribute.register `backwards_attribute

/-- Try to apply one of the given lemmas; it succeeds as soon as one of them succeeds. -/
meta def any_apply : list name → tactic name
| []      := failed
| (c::cs) := (mk_const c >>= apply >> pure c) <|> any_apply cs

meta def backwards_cautiously_attribute : user_attribute := {
  name := `backwards_cautiously,
  descr := "A lemma that should be applied to a goal whenever possible, as long as all arguments to the lemma by be fulfilled from existing hypotheses; use `backwards_reasoning` to automatically apply all lemmas tagged `backwards_cautiously`."
}

run_cmd attribute.register `backwards_cautiously_attribute

/- Try to apply one of the given lemmas, fulfilling all new goals using existing hypotheses. It succeeds if one of them succeeds. -/
meta def any_apply_no_new_goals : list name → tactic name
| []      := failed
| (c::cs) := (do n ← num_goals,
                 t ← mk_const c,
                 r ← seq (apply t >> skip) solve_by_elim,
                 n' ← num_goals,
                 guard (n = n' + 1),
                 pure c) <|> any_apply_no_new_goals cs

/-- Try to apply any lemma marked with the attribute @[backwards] -/
meta def backwards_reasoning : tactic string :=
do cs ← attribute.get_instances `backwards_cautiously,
   r ← try_core (any_apply_no_new_goals cs),
   match r with 
   | (some n) := return ("apply " ++ n.to_string ++ " ; solve_by_elim")
   | none     :=  do 
                    cs ← attribute.get_instances `backwards,
                    n ← any_apply cs | fail "no @[backwards] or @[backwards_cautiously] lemmas could be applied",
                    return ("apply " ++ n.to_string)
   end

attribute [backwards] subsingleton.elim

attribute [backwards] funext
attribute [backwards] set.ext   -- Order matters here: putting the attribute on set.ext after funext makes applicable prefer set.ext
attribute [backwards] propext
attribute [backwards] subtype.eq

universes u₁ u₂

@[backwards] definition empty_exfalso (x : false) : empty := begin exfalso, trivial end
@[backwards] definition pempty_exfalso (x : false) : pempty := begin exfalso, trivial end

@[backwards] lemma punit.ext (a b : punit.{u₁}): a = b := by induction a; induction b; refl
@[backwards] lemma ulift.ext {α : Type u₁} (X Y : ulift.{u₂} α) (w : X.down = Y.down) : X = Y :=
begin
  induction X, induction Y, dsimp at w, rw w,
end
@[backwards] lemma sigma.ext {α : Type u₁} (Z : α → Type u₂) (X Y : Σ a : α, Z a) (w1 : X.1 = Y.1) (w2 : @eq.rec_on _ X.1 _ _ w1 X.2 = Y.2) : X = Y :=
begin
  induction X, induction Y, dsimp at w1, dsimp at w2, induction w1, induction w2, refl,
end
@[backwards] lemma pair.ext {α : Type u₁} {β : Type u₂} {X Y : α × β} (p1 : X.1 = Y.1) (p2 : X.2 = Y.2) : X = Y := 
begin
  induction X, induction Y, dsimp at *, rw p1, rw p2,
end

-- TODO should `apply_instance` be in tidy? If so, these shouldn't be needed.
@[backwards] definition decidable_true  : decidable true  := is_true  dec_trivial
@[backwards] definition decidable_false : decidable false := is_false dec_trivial

attribute [backwards] quotient.mk quotient.sound

attribute [backwards_cautiously] eqv_gen.rel
attribute [backwards_cautiously] Exists.intro
