import data.polynomial

-- compare the result when you uncomment this import -- error!
-- import tidy.tidy

class algebra (R : out_param $ Type*) [comm_ring R] (A : Type*) extends ring A :=
(f : R → A) [hom : is_ring_hom f]
(commutes : ∀ r s, s * f r = f r * s)

variables (R : Type*) [ring R]

instance ring.to_ℤ_algebra : algebra ℤ R :=
{ f := coe,
  hom := by constructor; intros; simp,
  commutes := λ n r, int.induction_on n (by simp)
    (λ i ih, by simp [mul_add, add_mul, ih])
    (λ i ih, by simp [mul_add, add_mul, ih]), }
