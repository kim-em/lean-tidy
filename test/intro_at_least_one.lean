import tidy.intro_at_least_one
import tidy.force

example : ∀ x : ℕ, ∀ y : ℕ, true :=
begin
  intro_at_least_one,
  trivial,
end

example : true :=
begin
  success_if_fail { intro_at_least_one },
  trivial,
end

def f := ∀ x : ℕ, true
example : f :=
begin
  success_if_fail { force `[intros] },
  intro_at_least_one,
  trivial
end
