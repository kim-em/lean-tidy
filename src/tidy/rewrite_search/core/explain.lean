import .types

open interactive interactive.types expr tactic

variables {α β γ δ : Type}

namespace tidy.rewrite_search

def how.to_tactic (rule_strings : list string) : how → option string
| (how.rewrite index s location) := some ("nth_rewrite" ++ (match s with | side.L := "_lhs" | side.R := "_rhs" end) ++ " " ++ to_string location ++ " " ++ (rule_strings.nth index).iget)
| _ := none

def how.to_tactic_side (s : side) (rule_strings : list string) : how → option string
| (how.rewrite index _ location) := some ("nth_rewrite" ++ (match s with | side.L := "_lhs" | side.R := "_rhs" end) ++ " " ++ to_string location ++ " " ++ (rule_strings.nth index).iget)
| _ := none

meta def explain_proof (rule_strings : list string) (steps : list how) : string :=
string.intercalate ",\n" (steps.map $ λ s : how, (s.to_tactic rule_strings).to_list).join

meta def explain_proof' (ss : side) (rule_strings : list string) (steps : list how) : string :=
string.intercalate ",\n" (steps.map $ λ s : how, (s.to_tactic_side ss rule_strings).to_list).join

def how.concisely (rule_strings : list string) : how → option string
| (how.rewrite index side location) := some (rule_strings.nth index).iget
| _ := none

meta def explain_proof_concisely (rule_strings : list string) (steps : list how) (needs_refl : bool) : string :=
"erw [" ++ (string.intercalate ", " (steps.map $ λ s : how, (s.concisely rule_strings).to_list).join) ++ "]" ++ (if needs_refl then ", refl" else "")

-- fails if we can't just use rewrite
-- otherwise, returns 'tt' if we need a `refl` at the end
meta def check_if_simple_rewrite_succeeds (rewrites : list (expr × bool)) : tactic bool :=
lock_tactic_state $
focus1 $
do
  rewrites.mmap' (λ q : expr × bool, rewrite_target q.1 {symm := q.2, md := semireducible}),
  (reflexivity reducible >> return ff) <|> (reflexivity >> return tt)

meta def pp_rules (rs : list (expr × bool)) : tactic (list string) := rs.mmap (λ p, (do pp ← pretty_print p.1, return (if p.2 then ("←" ++ pp) else pp)))

meta def explain_proof_unit (cfg : config) (unit : proof_unit) : tactic string := do
  let steps := if unit.trans_start.is_none then unit.hows else unit.hows.reverse,
  rules_strings ← pp_rules cfg.rs,
  let rewrites := (steps.map $ λ s, match s with
                                  | how.rewrite index _ _ := [(cfg.rs.nth index).iget]
                                  | _ := []
                                  end).join,
  explanation ← (do
    -- FIXME `check_if_simple_rewrite_succeeds` won't work anymore, since it was designed
    -- for when we were considering the whole goal at once. Probably we can do two things,
    -- first give it a go to see if it solves the whole thing, then if that fails proceed as
    -- normal, and try to use the same thing on each proof unit, to simplify it. We could leave
    -- a TODO about how we could try to merge adjacent proof units or something, but currently
    -- (once implemented) only try the "most coarse" and "most fine" levels of simplication, not
    -- anywhere in between.

    -- Also the "sides" of the part above are probably broken now too.
    needs_refl ← check_if_simple_rewrite_succeeds rewrites,
    return (explain_proof_concisely rules_strings steps needs_refl)
  ) <|> return (explain_proof' (if unit.trans_start.is_none then side.L else side.R) rules_strings steps),
  return explanation

meta def explain_search_result (cfg : config) (proof : expr) (units : list proof_unit) : tactic string := do
  if cfg.trace then do
    pp ← pretty_print proof,
    trace format!"rewrite_search found proof:\n{pp}"
  else skip,

  -- FIXME drop the "transitivity" when this is the last unit, since it will be redundant.
  explanation ← to_string <$> list.join <$> units.mmap (λ u, do
    unit_expl ← explain_proof_unit cfg u,
    return $ (u.trans_start.to_list.map $ λ n, "transitivity " ++ n) ++ [unit_expl]
  ),

  if cfg.trace_result then trace explanation
  else skip,

  return explanation

end tidy.rewrite_search