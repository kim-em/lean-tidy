-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

definition {u v} transport {A : Type u} { P : A → Type v} {x y : A} (u : P x) (p : x = y) : P y :=
by induction p; exact u

@[simp] lemma {u v} congr_arg_refl {α : Sort u} {β : Sort v} (f : α → β) (a : α) : congr_arg f (eq.refl a) = eq.refl (f a) :=
begin
  refl,
end

@[simp] lemma {u v} congr_fun_refl {α : Sort u} {β : Sort v} (f : α → β) (a : α) : congr_fun (eq.refl f) a = eq.refl (f a) :=
begin
  refl,
end

@[simp] lemma {u v} congr_refl_arg {α : Sort u} {f₁ f₂ : α → Prop} (h₁ : f₁ = f₂) (a : α) : congr h₁ (eq.refl a) = congr_fun h₁ a :=
begin
  refl,
end

@[simp] lemma {u v} congr_refl_fun {α : Sort u} {f : α → Prop} (a b : α) (h : a = b) : congr (eq.refl f) h = congr_arg f h :=
begin
  refl,
end

@[simp] lemma symm_propext {a b : Prop} (p : a ↔ b) : eq.symm (propext p) = propext (p.symm) := by refl

@[simp] lemma {u} symm_refl {α : Sort u} (a : α) : eq.symm (eq.refl a) = eq.refl a := by refl  

@[simp] lemma {u v} symm_congr {α : Sort u} {β : Sort v} {f g : α → β} (h : f = g) {a b : α} (h' : a = b) : eq.symm (congr h h') = congr (eq.symm h) (eq.symm h') :=
begin
  refl,
end

@[simp] lemma {u v} symm_congr_fun {α : Sort u} {β : α → Sort v} {f g : Π x, β x} (h : f = g) (a : α) : eq.symm (congr_fun h a) = congr_fun (eq.symm h) a :=
begin
  refl,
end

@[simp] lemma {u v} symm_congr_arg {α : Sort u} {β : Sort v} {f : α → β} (a b : α) (h : a = b) : eq.symm (congr_arg f h) = congr_arg f (eq.symm h) :=
begin
  refl,
end

@[simp] lemma {u} symm_trans (a b c : Prop) (p : a = b) (q : b = c) : @eq.symm Prop a c (eq.trans p q) = @eq.trans Prop c b a (eq.symm q) (eq.symm p) := by refl

@[simp] lemma {u v w} eq.rec.congr_arg {α : Sort u} {β : Sort v} (f : α → β) {x y : α}  {C : β → Sort w} (p : C (f x)) (w : x = y): @eq.rec β (f x) C p _ (congr_arg f w) = @eq.rec α x (λ z, C (f z)) p _ w :=
begin
  induction w,
  refl,
end

@[simp] lemma {u v} parallel_transport_for_trivial_bundles {α : Sort u} {a b : α} {β : Sort v} (p : a = b) (x : β) : @eq.rec α a (λ a, β) x b p = x :=
begin
  induction p,
  refl,
end

@[simp] lemma {u l} eq.rec.trans {a b c : Prop} {C : Prop → Sort l} (z : C a) (p : a = b) (q : b = c) : @eq.rec _ a C z c (eq.trans p q) = @eq.rec _ b C (@eq.rec _ a C z b p) c q :=
begin
  induction p,
  induction q,
  refl,
end

@[simp] lemma {u} eq.rec.refl {α : Sort u} (a : α) (p : true = (a = a)): @eq.rec Prop true (λ (_x : Prop), _x) trivial (@eq α a a) p = eq.refl a := by refl


@[simp] lemma eq.mpr.trans {α β γ: Prop} (p : α = β) (q : β = γ) (g : γ) : eq.mpr (eq.trans p q) g = eq.mpr p (eq.mpr q g) :=
begin
  induction p,
  induction q,
  refl,
end

@[simp] lemma {u} eq.mpr.propext {α : Sort u} (a : α) : eq.mpr (propext (eq_self_iff_true a)) trivial = eq.refl a :=
begin
  refl,
end

@[simp] lemma {u} eq.mpr.refl {α : Sort u} (a b : α) (p : a = b) : (eq.mpr (congr_fun (congr_arg eq p) b) (eq.refl b)) = p :=
begin
  induction p,
  refl,
end