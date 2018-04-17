-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

definition {u v} transport {A : Type u} { P : A → Type v} {x y : A} (u : P x) (p : x = y) : P y :=
by induction p; exact u

@[simp] lemma {u v} congr_refl_arg {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} (h₁ : f₁ = f₂) (a : α) : congr h₁ (eq.refl a) = congr_fun h₁ a :=
begin
  reflexivity,
end

@[simp] lemma {u v} congr_refl_fun {α : Sort u} {β : Sort v} {f : α → β} (a b : α) (h : a = b) : congr (eq.refl f) h = congr_arg f h :=
begin
  reflexivity,
end

@[simp] lemma {u v} symm_congr_fun {α : Sort u} {β : α → Sort v} {f g : Π x, β x} (h : f = g) (a : α) : eq.symm (congr_fun h a) = congr_fun (eq.symm h) a :=
begin
  reflexivity,
end

@[simp] lemma {u v} symm_congr_arg {α : Sort u} {β : Sort v} {f : α → β} (a b : α) (h : a = b) : eq.symm (congr_arg f h) = congr_arg f (eq.symm h) :=
begin
  reflexivity,
end

@[simp] lemma {u₁ u₂} parallel_transport_for_trivial_bundles {α : Sort u₁} {a b : α} {β : Sort u₂} (p : a = b) (x : β) : @eq.rec α a (λ a, β) x b p = x :=
begin
  induction p,
  simp,
end
