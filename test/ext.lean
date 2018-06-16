import tactic.interactive

universes u₁ u₂

@[extensionality] lemma pair.ext {α : Type u₁} {β : Type u₂} {X Y : α × β} (p1 : X.1 = Y.1) (p2 : X.2 = Y.2) : X = Y := 
begin
  induction X, induction Y, dsimp at *, rw p1, rw p2,
end

lemma P (X Y : ℕ × ℕ) : X = X :=
begin
  ext, -- FIXME hopefully this will do something one day!
  apply pair.ext,
  refl,
  refl,
end