import group_theory.coset data.equiv data.quot
import tidy.tidy

open set function

section quotient_group

variable {α : Type*}

-- Some instances allowing us to use quotient notation
local attribute [instance] left_rel normal_subgroup.to_is_subgroup

-- We now prove two lemmas about elements in normal subgroups. I haven't attempted any automation here.
lemma quotient_group_aux  [group α] (s : set α) [normal_subgroup s] (a b : α) (h : a⁻¹ * b ∈ s) : a * b⁻¹ ∈ s :=
begin
  rw [← inv_inv a, ← mul_inv_rev],
  exact is_subgroup.inv_mem (is_subgroup.mem_norm_comm h),
end

lemma quotient_group_aux' [group α] (s : set α) [normal_subgroup s] (a b c d : α) (h₁ : a * b ∈ s) (h₂ : c * d ∈ s) : c * (a * (b * d)) ∈ s :=
begin
  apply is_subgroup.mem_norm_comm,
  rw [← mul_assoc, mul_assoc],
  apply (is_subgroup.mul_mem_cancel_right s h₁).2,
  exact is_subgroup.mem_norm_comm h₂
end
lemma quotient_group_aux'' [group α] (s : set α) [normal_subgroup s] (a b c d : α) (h₁ : a * b ∈ s) (h₂ : c * d ∈ s) : c * a * (b * d) ∈ s :=
begin
sorry
end

-- PROJECT one could write a tactic proving "all such" lemmas as above:
-- Given a word in α, write it as a vector in ℤ^α, and similarly write any hypotheses.
-- Now use Smith normal form (or perhaps Hermite normal form) to determine if there are solutions to the corresponding integer Diophantine equation.

-- Some 'hint' attributes for obviously.
local attribute [reducible] setoid_has_equiv left_rel
local attribute [applicable] is_submonoid.one_mem  -- `applicable` means the lemma should be applied whenever relevant
local attribute [semiapplicable] quotient_group_aux quotient_group_aux' quotient_group_aux'' -- `semiapplicable` means the lemma should be applied if all its hypotheses can be satisfied from the context
local attribute [simp] mul_assoc

instance quotient_group' [group α] (s : set α) [normal_subgroup s] : group (left_cosets s) :=
by refine 
{ one := ⟦1⟧,
  mul := λ a b, quotient.lift_on₂ a b (λ a b, ⟦a * b⟧) (by obviously),
  inv := λ a',  quotient.lift_on  a'  (λ a, ⟦a⁻¹⟧)     (by obviously),
  .. }; obviously

end quotient_group