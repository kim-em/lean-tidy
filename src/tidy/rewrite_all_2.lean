open tactic

def f (x : ℕ) := 2

example : f 1 = f 2 :=
begin
(do t ← target,
   trace t,
   a ← to_expr ``(f _),
   trace a,
   ty ← infer_type a,
   trace ty,
   k ← kabstract t a transparency.reducible ff,
   trace k,
   skip),
   refl
end


constant v : ℕ

example : 1 = 1 :=
begin
(do t ← target,
   let a := `(1),
   ty ← infer_type a,
   trace t,
   k ← kabstract t a,
   trace k,
   v ← mk_const `v,
   let w := expr.local_const `w `w binder_info.default ty,
   trace (k.instantiate_var v),
   trace (k.instantiate_var w),
   skip),
refl
end