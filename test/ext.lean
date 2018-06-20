import tactic.interactive

universes u₁ u₂

lemma Q : 1 = 1 :=
begin success_if_fail { ext }, refl end

lemma P (X Y : ℕ × ℕ) : X = X :=
begin
  ext,
  refl,
  refl,
end