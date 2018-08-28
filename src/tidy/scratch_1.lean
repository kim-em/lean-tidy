-- import .repeat_at_least_once
-- import .recover

-- open tactic

-- variables {α : Type} [has_to_format α]

-- meta inductive synthetic_goal
-- | none
-- | goals (original synthetic type : expr) : synthetic_goal

-- meta def synthetic_goal.new : tactic synthetic_goal :=
-- (do g :: gs ← get_goals,
--    t ← infer_type g,
--    is_lemma ← is_prop t,
--    if is_lemma then
--      return synthetic_goal.none
--    else do
--      m ← mk_meta_var t,
--      set_goals (m :: gs),
--      return (synthetic_goal.goals g m t)) <|> return synthetic_goal.none

-- meta def synthetic_goal.update : synthetic_goal → tactic synthetic_goal
-- | synthetic_goal.none := synthetic_goal.new
-- | (synthetic_goal.goals g g' t) := 
--     do try_core (do {
--       val ← instantiate_mvars g',
--       do {
--         guard (val.metavariables = []),
--         c  ← new_aux_decl_name,
--         gs ← get_goals,
--         set_goals [g],
--         add_aux_decl c t val ff >>= unify g,
--         set_goals gs } <|> unify g val }),
--       synthetic_goal.new

-- meta def luxembourg_chain_aux (tac : tactic α) : ℕ → synthetic_goal → tactic (synthetic_goal × list (ℕ × α))
-- | b s := do (done >> return (s, [])) <|>
--             (do a ← tac,
--                 (s, c) ← luxembourg_chain_aux 0 s,
--                 return (s, (b, a) :: c)) <|>
--             (do s ← s.update,
--                 n ← num_goals,
--                 if b = (n-1) then return (s, []) else do  
--                 rotate_left 1,
--                 luxembourg_chain_aux (b+1) s)    

-- /-- Returns a `list (ℕ × α)`, whose successive elements `(n, a)` represent
--     a successful result of `rotate_left n >> tac`. 
    
--     (When `n = 0`, the `rotate_left` may of course be omitted.) -/
-- meta def luxembourg_chain_core (tac : tactic α) : tactic (list (ℕ × α)) :=
-- do b ← num_goals,
--    s ← synthetic_goal.new,
--    (s, r) ← luxembourg_chain_aux tac 0 s,
--    s.update,
--    return r


-- meta def luxembourg_chain (tactics : list (tactic α)) : tactic (list string) :=
-- do results ← luxembourg_chain_core (first tactics),
--    return (results.map (λ p, (if p.1 = 0 then "" else "rotate_left " ++ (to_string p.1) ++ ", ") ++ (format!"{p.2}").to_string))
