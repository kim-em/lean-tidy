-- -- FIXME this is all junk

-- universe u

-- open tactic

-- example ( f : if tt = ff then empty else unit ) : unit.star = f :=
-- begin
--   (do (s, u) ← mk_simp_set ff [] [], h ← local_context, t ← infer_type h.head, r ← simplify s [] t {} `eq skip, trace t, trace r),  -- says "(unit, ...proof...)"
--   (do (s, u) ← mk_simp_set ff [] [], h ← local_context, t ← infer_type h.head, r ← s.dsimplify [`ite, `bool.decidable_eq, `bool.decidable_eq._main] t {}, trace t, trace r), -- says "unit"
--   (do (s, u) ← mk_simp_set ff [] [], h ← local_context, t ← infer_type h.head, r ← s.dsimplify [`ite] t {md:=semireducible}, trace t, trace r), -- says "unit"
--   -- (do (s, u) ← mk_simp_set ff [] [], h ← local_context, t ← infer_type h.head, r ← s.dsimplify [] t {md:=transparency.all}, trace t, trace r), -- says "dsimplify tactic failed to simplify"
--   sorry
-- end

-- #check ite

-- def ite' (c : Prop) [h : decidable c] {α : Sort u} (t e : α) : α :=
-- decidable.rec_on h (λ hnc, e) (λ hc, t)

-- meta def names_in_expr_core : expr → list name → list name 
-- | (expr.app a b) l := names_in_expr_core a (names_in_expr_core b l)
-- | (expr.const n _) l := n :: l
-- | (expr.lam _ _ a b) l := names_in_expr_core a (names_in_expr_core b l) -- FIXME is this actually how lam works?
-- | (expr.pi _ _ a b) l := names_in_expr_core a (names_in_expr_core b l)  -- ?
-- | (expr.elet _ a b c) l := names_in_expr_core a (names_in_expr_core b (names_in_expr_core c l)) -- ?
-- | _ l := l
-- .

-- meta def first_name_in_expr_core : expr → option name → option name 
-- | _ (some n) := some n
-- | (expr.app a b) none := first_name_in_expr_core b (first_name_in_expr_core a none)
-- | (expr.const n _) none := some n
-- | (expr.lam _ _ a b) none := first_name_in_expr_core b (first_name_in_expr_core a none)
-- | (expr.pi _ _ a b) none := first_name_in_expr_core b (first_name_in_expr_core a none)
-- | (expr.elet _ a b c) none := first_name_in_expr_core c (first_name_in_expr_core b (first_name_in_expr_core a none))
-- | _ _ := none
-- .

-- meta def names_in_expr (e : expr) : tactic (list name) := pure (names_in_expr_core e [])
-- meta def first_name_in_expr (e : expr) : tactic (option name) := pure (first_name_in_expr_core e none)

-- meta def dunfold_everything (e : expr) := do names ← names_in_expr e,
--                                              dunfold names e
-- meta def dunfold_first_name (e : expr) := do name ← first_name_in_expr e,
--                                              match name with
--                                              | none := failed
--                                              | (some n) := dunfold [n] e
--                                              end

-- example ( f : ite' (tt = ff) empty unit ) : unit.star = f :=
-- begin
--   (do (s, u) ← mk_simp_set ff [] [], h ← local_context, t ← infer_type h.head, r ← simplify s [] t {} `eq skip, trace t, trace r),  -- says "(unit, ...proof...)"
--   (do (s, u) ← mk_simp_set ff [] [], h ← local_context, t ← infer_type h.head, r ← s.dsimplify [`ite', `bool.decidable_eq, `bool.decidable_eq._main] t {}, trace t, trace r), -- says "unit"
--   (do (s, u) ← mk_simp_set ff [] [], h ← local_context, t ← infer_type h.head, r ← s.dsimplify [`ite'] t {md:=semireducible}, trace t, trace r), -- says "unit"
--     revert f,
--     target >>= names_in_expr >>= trace,
--     target >>= dunfold_first_name >>= trace,
--     target >>= dunfold_everything >>= trace,
--     intro f,
--     dunfold ite' at f,
--   (do (s, u) ← mk_simp_set ff [] [], h ← local_context, t ← infer_type h.head, r ← s.dsimplify [] t {md:=transparency.all, unfold_reducible:=tt}, trace t, trace r), -- says "dsimplify tactic failed to simplify"
--   sorry
-- end


-- example ( f : if tt = ff then empty else unit ) : unit.star = f :=
-- begin
-- have h : f = @cast _ unit (by simp) f, 
--   { simp [cast_eq] },
--   rw h,
--   generalize : cast _ f = g, 
--   clear h f,
--   induction g,
--   refl
-- end
