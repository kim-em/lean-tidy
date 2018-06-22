import tactic.interactive

variable (α : Type)
def foo : semigroup α := 
begin
  refine_struct ({ .. } : semigroup α),
end
