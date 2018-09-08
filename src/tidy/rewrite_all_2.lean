import .lock_tactic_state

open tactic

def f (x : ℕ) (y : ℕ) := 2

meta def repeat_kabstract_core (e : tactic (expr × list expr)) : expr → list (expr × list expr) → tactic (expr × list (expr × list expr))
| t results := do
  (e', mvars) ← e,
  r ← try_core (do r ← kabstract t e', guard r.has_var, return r),
  match r with
  | none := return (t, results)
  | (some t') := do 
    ty ← infer_type e',
    -- n ← mk_fresh_name,
    -- let w := expr.local_const n n binder_info.default ty,
    w ← mk_meta_var ty,
    t'' ← return $ t'.instantiate_var w,
    mvars' ← mvars.mmap instantiate_mvars,
    repeat_kabstract_core t'' ((w, mvars') :: results)
  end   

meta def substitutions_core : expr → list expr → 
  tactic (tactic (expr × list expr) × (list expr → tactic expr) × (list expr → tactic expr))
| (expr.pi n bi d b) types := 
  do substitutions_core b (d :: types)          
| `(%%lhs = %%rhs) types := 
  do let fresh_mvars := (do mvars ← types.mmap mk_meta_var,
                           let pattern := lhs.instantiate_vars mvars,
                           return (pattern, mvars)),
     let lhs_replacer : list expr → tactic expr := (λ values, return (lhs.instantiate_vars values)),
     let rhs_replacer : list expr → tactic expr := (λ values, return (rhs.instantiate_vars values)),
     return (fresh_mvars, lhs_replacer, rhs_replacer)
| _ _ := failed

/-- Given a lemma `eq`, returns three tactics.
    1) returning `(lhs', mvars)` where `lhs'` is a copy of the left hand side of the lemma, with
    variables replaced by fresh metavariables `mvars`.
    2) taking a list of expressions, and returning `lhs'`, the left hand side with variables
    instantiated with these values.
    3) as with 2), but for the right hand side. -/
meta def substitutions (eq : expr) : tactic (tactic (expr × list expr) × (list expr → tactic expr) × (list expr → tactic expr)) :=
substitutions_core eq []

universe u

def list.rotate_left {α : Type u} (L : list α) (n : ℕ) := L.drop n ++ L.take n

def list.rotations {α : Type u} (L : list α) : list (list α) :=
(list.range L.length).map $ λ n, L.rotate_left n

/-- `repeat_kabstract t eq` repeatedly calls `kabstract` on `t`, 
    looking for subexpressions matching the lhs, after binders, of `eq`. 
    After each call, the local variable is replaced with a local constant, and the
    bindings of metavariables in `e` are recorded.
    
    The result consists of `(t', L)`, where `t'` is `t` with subexpressions replaced by local
    constants. The list `L` contains pairs `(n, M)`, where `n` is one of the local constants,
    and `M` is the list of values of metavariables for that replacement. -/
meta def repeat_kabstract (t eq : expr) : tactic unit :=
do (lhs_matcher, lhs_substituter, rhs_substituter) ← substitutions eq,
  (t', mvars) ← repeat_kabstract_core lhs_matcher t [],
  trace t',
  trace mvars,
  let substituter : list (expr × list expr) → tactic expr := λ mvars,
    lock_tactic_state $ 
    (do m_h :: m_t ← return mvars,
       rhs ← rhs_substituter m_h.2,
       unify rhs m_h.1,
       m_t.mmap (λ p, do lhs ← lhs_substituter p.2, unify lhs p.1),
       instantiate_mvars t'),
  t' ← mvars.rotations.mmap substituter,
  -- t' ← substituter mvars,
  trace t',
  skip

lemma fx (n : ℕ) (m : ℕ) : f n m = f 17 19 := sorry

example : [f 1 2, 3, f 2 5] = [f 3 1, f 4 1] :=
begin
(do `(%%lhs = %%rhs) ← target,
    trace lhs,
    eq ← mk_const `fx,
    trace eq,
    ty ← infer_type eq,
    r ← repeat_kabstract lhs ty,
    trace r
)
end

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
   n ← mk_fresh_name,
   let w := expr.local_const n `w binder_info.default ty,
   k ← return $ k.instantiate_var w,
   a' ← to_expr ``(f _),
   k' ← kabstract k a' transparency.reducible ff,
   trace k',
   n ← mk_fresh_name,
   let w := expr.local_const n `w binder_info.default ty,
   k' ← return $ k'.instantiate_var w,
   trace k',
   a'' ← to_expr ``(f _),
   k'' ← kabstract k' a'' transparency.reducible ff,
   trace k'',
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