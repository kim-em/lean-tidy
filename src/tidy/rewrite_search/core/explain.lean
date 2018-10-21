import .types

open interactive interactive.types expr tactic

variables {α β γ δ : Type}

namespace tidy.rewrite_search

private meta def hand : sided_pair string := ⟨"lhs", "rhs"⟩

meta def nth_rule (cfg : config) (i : ℕ) : expr × bool := (cfg.rs.nth i).iget

meta def pp_rule (r : expr × bool) : tactic string :=
  do pp ← pretty_print r.1, return $ (if r.2 then "←" else "") ++ pp

meta def how.to_rewrite (cfg : config) : how → option (expr × bool)
| (how.rewrite index _) := nth_rule cfg index
| _ := none

meta def how.explain (cfg : config) (s : side) : how → tactic (option string)
| (how.rewrite index location) := do
  rule ← pp_rule $ nth_rule cfg index,
  return $ some ("nth_rewrite_" ++ hand.get s ++ " " ++ to_string location ++ " " ++ rule)
| _ := return none

meta def explain_rewrites_full (cfg : config) (s : side) (steps : list how) : tactic string := do
  rules ← steps.mmap $ λ h : how, option.to_list <$> h.explain cfg s,
  return $ string.intercalate ",\n" rules.join

meta def explain_rewrites_concisely (steps : list (expr × bool)) (needs_refl : bool) : tactic string := do
  rules ← string.intercalate ", " <$> steps.mmap pp_rule,
  return $ "erw [" ++ rules ++ "]" ++ (if needs_refl then ", refl" else "")

-- fails if we can't just use rewrite
-- otherwise, returns 'tt' if we need a `refl` at the end
meta def check_if_simple_rewrite_succeeds (rewrites : list (expr × bool)) (goal : expr) : tactic bool :=
lock_tactic_state $ do
  m ← mk_meta_var goal,
  set_goals [m],
  rewrites.mmap' $ λ q : expr × bool, rewrite_target q.1 {symm := q.2, md := semireducible},
  (reflexivity reducible >> return ff) <|> (reflexivity >> return tt)

meta def proof_unit.rewrites (u : proof_unit) (cfg : config) : list (expr × bool) :=
  u.steps.filter_map $ how.to_rewrite cfg

-- TODO rewrite this to use conv!
meta def proof_unit.explain (u : proof_unit) (cfg : config) : tactic string := do
  -- TODO We could try to merge adjacent proof units or something more complicated.
  -- Currently we only try the "most coarse" (whole proof) and "most fine" (proof_unit
  -- level) levels of simplication, not anywhere in between.
  (do
    goal ← infer_type u.proof,
    let rewrites := u.rewrites cfg,
    needs_refl ← check_if_simple_rewrite_succeeds rewrites goal,
    explain_rewrites_concisely rewrites needs_refl
  ) <|> explain_rewrites_full cfg u.side u.steps

meta def explain_proof_full (cfg : config) : list proof_unit → tactic string
| [] := return ""
| (u :: rest) := do
  -- This is an optimisation: don't use transitivity for the last unit, since
  -- it neccesarily must be redundant.
  head ← if rest.length = 0 ∨ u.side = side.L then pure [] else (do
    n ← infer_type u.proof >>= rw_equation.rhs >>= pretty_print,
    pure $ ["transitivity " ++ n]
  ),

  unit_expl ← u.explain cfg,
  rest_expl ← explain_proof_full rest,
  let expls := (head ++ [unit_expl, rest_expl]).filter $ λ t, ¬(t.length = 0),
  return $ string.intercalate ",\n" expls

meta def explain_proof_concisely (cfg : config) (proof : expr) (l : list proof_unit) : tactic string := do
  let rws : list (expr × bool) := list.join $ l.map (λ u, do
    (r, s) ← u.rewrites cfg,
    return (r, if u.side = side.L then s else ¬s)
  ),
  goal ← infer_type proof,
  needs_refl ← check_if_simple_rewrite_succeeds rws goal,
  explain_rewrites_concisely rws needs_refl

meta def explain_search_result (cfg : config) (proof : expr) (units : list proof_unit) : tactic string := do
  if cfg.trace then do
    pp ← pretty_print proof,
    trace format!"rewrite_search found proof:\n{pp}"
  else skip,

  explanation ← explain_proof_concisely cfg proof units <|> explain_proof_full cfg units,
  if cfg.trace_result then trace $ "/- `rewrite_search` says -/\n" ++ explanation
  else skip,
  return explanation

end tidy.rewrite_search