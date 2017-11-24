import ..tidy

open tactic

def tidy_test_0 : ∀ x : unit, x = unit.star := 
begin
  success_if_fail { chain [ interactive_simp ] },
  intro1,
  induction x,
  refl
end
def tidy_test_1 (a : string): ∀ x : unit, x = unit.star := 
begin
  tidy {show_hints := tt}
end
def tidy_test_2 (a : string): ∀ x : unit, x = unit.star := 
begin
  tidy {hints := [7,4]}
end
