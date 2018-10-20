import .types

open interactive interactive.types expr tactic

variables {α β γ δ : Type}

namespace tidy.rewrite_search

def how.to_tactic (rule_strings : list string) : how → option string
| (how.rewrite index s location) := some ("nth_rewrite" ++ (match s with | side.L := "_lhs" | side.R := "_rhs" end) ++ " " ++ to_string location ++ " " ++ (rule_strings.nth index).iget)
| _ := none

meta def explain_proof (rule_strings : list string) (steps : list how) : string :=
string.intercalate ",\n" (steps.map $ λ s : how, (s.to_tactic rule_strings).to_list).join

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

meta def explain_search_result' (cfg : config) (proof : expr) (steps : list how) : tactic string := do
  if cfg.trace then do
  pp ← pretty_print proof,
  trace format!"rewrite_search found proof:\n{pp}"
  else skip,
  rules_strings ← pp_rules cfg.rs,
  let rewrites := (steps.map $ λ s, match s with
                                  | how.rewrite index _ _ := [(cfg.rs.nth index).iget]
                                  | _ := []
                                  end).join,
  explanation ← (do
    needs_refl ← check_if_simple_rewrite_succeeds rewrites,
    return (explain_proof_concisely rules_strings steps needs_refl)
  ) <|> return (explain_proof rules_strings steps),
  if cfg.trace_result then trace explanation
  else skip,
  return explanation

meta def explain_search_result (cfg : config) (proof : expr) (steps : list proof_unit) : tactic string := do
  -- FIXME introduce suppose for general `proof_unit` structures
  match steps with
  | [u] := if u.trans_start.is_none then explain_search_result' cfg proof u.hows
    else explain_search_result' cfg proof u.hows.reverse
  | [u1, u2] := if ¬(u1.trans_start.is_none ∧ u2.trans_start.is_some) then return "<???>"
    else explain_search_result' cfg proof (u1.hows ++ u2.hows.reverse)
  | _ := return "<???>"
  end

end tidy.rewrite_search