import tactic.chain

open tactic

set_option trace.chain true

def F : 1 = 1 ∧ 2 = 2 :=
begin
  chain [`[refl], `[split]],
end

#print F

def G : ℕ × ℕ :=
begin
  chain [`[split]],
  chain [`[exact 0]],
end

#print G
#print G._aux_1

