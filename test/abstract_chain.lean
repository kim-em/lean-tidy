import tidy.abstract_chain

def F : 1 = 1 ∧ 2 = 2 :=
begin
  abstract_chain {trace_steps:=tt} [`[refl], `[split]],
end

#print F
#print F._aux_3

def G : ℕ × ℕ :=
begin
  abstract_chain {trace_steps:=tt} [`[split]],
  abstract_chain {trace_steps:=tt} [`[exact 0]],
end

#print G
#print G._aux_1

open tactic

structure C :=
(a : ℕ)
(b : a > 0)
(c : array a ℕ)

def H : C :=
begin
abstract foo { split, rotate 2, exact 1, abstract { exact dec_trivial }, split, abstract bar { intros, exact 0 } }
end

set_option pp.proofs true
#print H   -- def H : C := H.foo