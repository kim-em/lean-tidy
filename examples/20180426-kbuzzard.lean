import data.set.lattice
import tidy.tidy

-- Can we do this?
example (X : Type) (R : Type) (D : R → set X) (γ : Type) (f : γ → R) :
  ⋃₀(D '' set.range f) = ⋃ (i : γ), D (f i) := 
begin
-- fapply _root_.funext,
-- intros,
-- fapply propext,
-- fsplit,
-- intros,
-- cases a,
-- cases a_h,
-- cases a_h_w,
-- cases a_h_w_h,
-- induction a_h_w_h_right, cases a_h_w_h_left,
-- induction a_h_w_h_left_h,
-- fsplit, -- Things go wrong here!
-- tidy {max_steps:=1,trace_result:=tt},

--- Kevin's proof
  apply set.ext,
  intro x,
  split,
  intro H,
  cases H with V HV,
  cases HV with HV HX,
  cases HV with r HR,
  cases HR.1 with i Hi,
  existsi V,
  existsi _,
  assumption,
  simp,
  existsi i,
  rw Hi,rw HR.2,

  intro H,
  cases H with V HV,
  cases HV with HV Hx,
  cases HV with i Hi,
  existsi V,
  existsi _,
  assumption,
  existsi (f i),
  split,
  simp,
  existsi i,
  refl,
  rw Hi,
end