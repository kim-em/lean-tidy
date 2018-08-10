import tidy.forwards_reasoning

@[forwards] lemma G (n : ℕ) : list ℕ := [n]

example : 1 = 1 :=
begin 
  success_if_fail { forwards_reasoning },
  refl
end

@[forwards] lemma F : ℕ := 0

example : 1 = 1 :=
begin 
  forwards_reasoning,
  forwards_reasoning,
  refl
end

example : 1 = 1 :=
begin 
  have p := [0],  
  forwards_reasoning,
  success_if_fail { forwards_reasoning },
  refl
end