import tidy.force

-- open tactic

example : ∀ x : ℕ, 1 = 1 :=
begin
 intros,
 success_if_fail { force `[intros] },
 refl
end