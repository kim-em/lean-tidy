import tidy.simplify_proof
open tactic

meta def f := `[exact (id (eq.refl 0))]
def z (h : 0 = 0) : 1 = 1 := sorry

structure P :=
(a : ∀ n : ℕ, 0 = 0)
(b : 1 = 1)

set_option pp.proofs true

lemma g : P :=
begin
simplify_proof split,
simplify_proof intros,
simplify_proof f,
simplify_proof `[{apply z, f}],
end

#print g