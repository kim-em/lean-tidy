import tidy.tidy

inductive slice 
| pos : ℕ → slice 
| neg : ℕ → slice 
| cup : ℕ → slice 
| cap : ℕ → slice

open slice

inductive diagram
| nil
| cons : slice → diagram → diagram

infixr ` ~~ `:80 := diagram.cons
notation `t[` l:(foldr `, ` (h t, diagram.cons h t) diagram.nil `]`) := l



namespace isotopy
variable (d : diagram)
axiom commute_pos_pos (n m) (h : n ≥ m + 2) : (pos n) ~~ (pos m) ~~ d = (pos m) ~~ (pos n) ~~ d
axiom commute_pos_neg (n m) (h : n ≥ m + 2) : (pos n) ~~ (neg m) ~~ d = (neg m) ~~ (pos n) ~~ d
axiom commute_neg_pos (n m) (h : n ≥ m + 2) : (neg n) ~~ (pos m) ~~ d = (pos m) ~~ (neg n) ~~ d
axiom commute_neg_neg (n m) (h : n ≥ m + 2) : (neg n) ~~ (neg m) ~~ d = (neg m) ~~ (neg n) ~~ d

axiom commute_cup_pos (n m) (h : n ≥ m + 2) : (cup n) ~~ (pos m) ~~ d = (pos m) ~~ (cup n) ~~ d 
axiom commute_cup_neg (n m) (h : n ≥ m + 2) : (cup n) ~~ (neg m) ~~ d = (neg m) ~~ (cup n) ~~ d 
axiom commute_cap_pos (n m) (h : n ≥ m + 2) : (cap n) ~~ (pos m) ~~ d = (pos m) ~~ (cap n) ~~ d 
axiom commute_cap_neg (n m) (h : n ≥ m + 2) : (cap n) ~~ (neg m) ~~ d = (neg m) ~~ (cap n) ~~ d 

axiom commute_pos_cup (n m) (h : n ≥ m)     : (pos n) ~~ (cup m) ~~ d = (cup m) ~~ (pos (n+2)) ~~ d 
axiom commute_pos_cap (n m) (h : n ≥ m + 2) : (pos n) ~~ (cap m) ~~ d = (cap m) ~~ (pos (n-2)) ~~ d 
axiom commute_neg_cup (n m) (h : n ≥ m)     : (neg n) ~~ (cup m) ~~ d = (cup m) ~~ (neg (n+2)) ~~ d 
axiom commute_neg_cap (n m) (h : n ≥ m + 2) : (neg n) ~~ (cap m) ~~ d = (cap m) ~~ (neg (n-2)) ~~ d 

axiom commute_cup_cup (n m) (h : n ≥ m)     : (cup n) ~~ (cup m) ~~ d = (cup m) ~~ (cup (n+2)) ~~ d 
axiom commute_cup_cap (n m) (h : n ≥ m + 2) : (cup n) ~~ (cap m) ~~ d = (cap m) ~~ (cup (n-2)) ~~ d 
axiom commute_cap_cup (n m) (h : n ≥ m)     : (cap n) ~~ (cup m) ~~ d = (cup m) ~~ (cap (n+2)) ~~ d 
axiom commute_cap_cap (n m) (h : n ≥ m + 2) : (cap n) ~~ (cap m) ~~ d = (cap m) ~~ (cap (n-2)) ~~ d 

axiom zigzag_left (n : ℕ) : (cup n) ~~ (cap (n+1)) ~~ d = d  
axiom zigzag_right (n : ℕ) : (cup (n+1)) ~~ (cap n) ~~ d = d

axiom R2_east (n : ℕ) : (neg n) ~~ (pos n) ~~ d = d
axiom R2_west (n : ℕ) : (pos n) ~~ (neg n) ~~ d = d
axiom R2_north (n : ℕ) : (cup (n+1)) ~~ (pos n) ~~ (neg (n+2)) ~~ cap(n+1) ~~ d = (cap n) ~~ (cup n) ~~ d
axiom R2_south (n : ℕ) : (cup (n+1)) ~~ (neg n) ~~ (pos (n+2)) ~~ cap(n+1) ~~ d = (cap n) ~~ (cup n) ~~ d

axiom R1_pos_east (n : ℕ) : (cup (n+1)) ~~ (pos n) ~~ (cap (n+1)) ~~ d = d
axiom R1_neg_east (n : ℕ) : (cup (n+1)) ~~ (neg n) ~~ (cap (n+1)) ~~ d = d
axiom R1_pos_west (n : ℕ) : (cup n) ~~ (pos (n+1)) ~~ (cap n) ~~ d = d
axiom R1_neg_west (n : ℕ) : (cup n) ~~ (neg (n+1)) ~~ (cap n) ~~ d = d
axiom R1_pos_north (n : ℕ) : (pos n) ~~ (cap n) ~~ d = (cap n) ~~ d
axiom R1_neg_north (n : ℕ) : (neg n) ~~ (cap n) ~~ d = (cap n) ~~ d
axiom R1_pos_south (n : ℕ) : (cup n) ~~ (pos n) ~~ d = (cup n) ~~ d
axiom R1_neg_south (n : ℕ) : (cup n) ~~ (neg n) ~~ d = (cup n) ~~ d

axiom R3_pos_pos_pos (n : ℕ) : (pos n) ~~ (pos (n+1)) ~~ (pos n) ~~ d = (pos (n+1)) ~~ (pos n) ~~ (pos (n+1)) ~~ d
axiom R3_pos_pos_neg (n : ℕ) : (pos n) ~~ (pos (n+1)) ~~ (neg n) ~~ d = (neg (n+1)) ~~ (pos n) ~~ (pos (n+1)) ~~ d
axiom R3_pos_neg_neg (n : ℕ) : (pos n) ~~ (neg (n+1)) ~~ (neg n) ~~ d = (neg (n+1)) ~~ (neg n) ~~ (pos (n+1)) ~~ d
axiom R3_neg_pos_pos (n : ℕ) : (neg n) ~~ (pos (n+1)) ~~ (pos n) ~~ d = (pos (n+1)) ~~ (pos n) ~~ (neg (n+1)) ~~ d
axiom R3_neg_neg_pos (n : ℕ) : (neg n) ~~ (neg (n+1)) ~~ (pos n) ~~ d = (pos (n+1)) ~~ (neg n) ~~ (neg (n+1)) ~~ d
axiom R3_neg_neg_neg (n : ℕ) : (neg n) ~~ (neg (n+1)) ~~ (neg n) ~~ d = (neg (n+1)) ~~ (neg n) ~~ (neg (n+1)) ~~ d

axiom cap_over  (n : ℕ) : (pos n) ~~ (cap (n+1)) ~~ d = (neg (n+1)) ~~ (cap n) ~~ d
axiom cap_under (n : ℕ) : (neg n) ~~ (cap (n+1)) ~~ d = (pos (n+1)) ~~ (cap n) ~~ d
axiom cup_over  (n : ℕ) : (cup (n+1)) ~~ (neg n) ~~ d = (cup n) ~~ (pos (n+1)) ~~ d
axiom cup_under (n : ℕ) : (cup (n+1)) ~~ (pos n) ~~ d = (cup n) ~~ (neg (n+1)) ~~ d

-- axiom rotate_pos_clockwise   (n : ℕ) : (cup n) ~~ (pos (n+1)) ~~ (cap (n+2)) ~~ d = (neg n) ~~ d
-- axiom rotate_neg_clockwise   (n : ℕ) : (cup n) ~~ (neg (n+1)) ~~ (cap (n+2)) ~~ d = (pos n) ~~ d
-- axiom rotate_pos_widdershins (n : ℕ) : (cup (n+2)) ~~ (pos (n+1)) ~~ (cap n) ~~ d = (neg n) ~~ d
-- axiom rotate_neg_widdershins (n : ℕ) : (cup (n+2)) ~~ (neg (n+1)) ~~ (cap n) ~~ d = (pos n) ~~ d

attribute [search] commute_pos_pos commute_pos_neg commute_neg_pos commute_neg_neg
attribute [search] commute_cup_pos commute_cup_neg commute_cap_pos commute_cap_neg
attribute [search] commute_pos_cup commute_pos_cap commute_neg_cup commute_neg_cap
attribute [search] commute_cup_cup commute_cup_cap commute_cap_cup commute_cap_cap
attribute [search] zigzag_left zigzag_right
attribute [search] cap_over cap_under cup_over cup_under
attribute [search] R1_pos_east R1_neg_east R1_pos_west R1_neg_west R1_pos_north R1_neg_north R1_pos_south R1_neg_south
attribute [search] R2_east R2_west R2_north R2_south
attribute [search] R3_pos_pos_pos R3_pos_pos_neg R3_pos_neg_neg R3_neg_pos_pos R3_neg_neg_pos R3_neg_neg_neg 
-- attribute [search] rotate_pos_clockwise rotate_neg_clockwise rotate_pos_widdershins rotate_neg_widdershins

end isotopy

namespace norm_num
open tactic

meta def derive' : expr → tactic (expr × expr) | e :=
do (_, e', pr) ←
    ext_simplify_core () {} simp_lemmas.mk (λ _, failed) (λ _ _ _ _ _, failed)
      (λ _ _ _ _ e,
        do (new_e, pr) ← derive1 derive' e,
           guard (¬ new_e =ₐ e),
           return ((), new_e, some pr, tt))
      `eq e,
    return (e', pr)
end norm_num

open isotopy
open tactic

meta def isotopy := `[rewrite_search_using [`search] { discharger := `[norm_num], simplifier := norm_num.derive, trace_result := tt }]
meta def isotopy' := `[rewrite_search_using [`search] { discharger := `[norm_num], simplifier := norm_num.derive, trace := tt, view := visualiser, trace_result := tt }]

lemma commute_1 : t[pos 0, neg 2, pos 4] = t[pos 4, neg 2, pos 0] := by isotopy
lemma commute_2 : t[cup 0, pos 2] = t[pos 0, cup 0] := by isotopy
lemma commute_3 : t[cup 2, cap 0] = t[cup 0, cap 2] := by isotopy

lemma bulge : t[cup 1, cap 0, cup 0, cap 1] = t[] := by isotopy

lemma R2_north : t[cup 1, pos 0, neg 2, cap 1] = t[cap 0, cup 0] := by isotopy

lemma twists : t[cup 0, cup 2, pos 0, pos 2, cap 1, cap 0] = t[cup 0, cap 0] := by isotopy
-- begin
-- rw commute_cup_pos,
-- rw R1_pos_south,
-- rw R1_pos_south,
-- rw zigzag_right,
-- norm_num
-- end

lemma rotate : t[cup 0, pos 1, cap 2] = t[neg 0] := by isotopy

-- lemma recognise_trefoil : t[cup 0, cup 1, pos 0, pos 0, pos 0, cap 1, cap 0] = t[cup 0, cup 2, neg 1, pos 0, pos 2, cap 1, cap 0] := by isotopy