-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison

import tidy.rewrite_all
import .init

open interactive interactive.types expr tactic

namespace tidy.rewrite_search

def how.to_tactic (rule_strings : list string) : how → option string 
| (how.defeq) := none
| (how.rewrite index s location) := some ("nth_rewrite" ++ (match s with | side.L := "_lhs" | side.R := "_rhs" end) ++ " " ++ to_string location ++ " " ++ (rule_strings.nth index).iget)

meta def explain_proof (rule_strings : list string) (steps : list how) : string :=
string.intercalate ",\n" (steps.map $ λ s : how, (s.to_tactic rule_strings).to_list).join

def how.concisely (rule_strings : list string) : how → option string
| (how.defeq) := none
| (how.rewrite index side location) := some (rule_strings.nth index).iget

meta def explain_proof_concisely (rule_strings : list string) (steps : list how) (needs_refl : bool) : string :=
"erw [" ++ (string.intercalate ", " (steps.map $ λ s : how, (s.concisely rule_strings).to_list).join) ++ "]" ++ (if needs_refl then ", refl" else "")

-- fails if we can't just use rewrite
-- otherwise, returns 'tt' if we need a `refl` at the end
meta def check_if_simple_rewrite_succeeds (rewrites : list (expr × bool)) : tactic bool :=
lock_tactic_state $
focus1 $
do
  t ← target,
  rewrites.mmap' (λ q : expr × bool, rewrite_target q.1 {symm := q.2, md := semireducible}),
  (reflexivity reducible >> return ff) <|> (reflexivity >> return tt)

meta def pp_rules (rs : list (expr × bool)) : tactic (list string) := rs.mmap (λ p, (do pp ← pretty_print p.1, return (if p.2 then ("←" ++ pp) else pp)))

meta def handle_search_result {α β γ : Type} (cfg : config α β γ) (rules : list (expr × bool)) (result : search_result) : tactic string := do
match result with
| search_result.failure reason      := fail reason
| search_result.success proof steps := do
    if cfg.trace then do
      pp ← pretty_print proof,
      trace format!"rewrite_search found proof:\n{pp}"
    else skip,
    rules_strings ← pp_rules rules,
    explanation ← (do 
      let rewrites := (steps.map $ λ s, match s with
                                   | how.defeq := []
                                   | how.rewrite index _ _ := [(rules.nth index).iget]
                                   end).join,
      needs_refl ← check_if_simple_rewrite_succeeds rewrites,
      return (explain_proof_concisely rules_strings steps needs_refl)) <|> return (explain_proof rules_strings steps),
    if cfg.trace_result then trace explanation          
    else skip,
    exact proof,
    return explanation
end

meta def do_rewrite_search {α β γ : Type} (rs : list (expr × bool)) (cfg : config α β γ) : tactic string := do
  t ← target,
  match t with
  | `(%%lhs = %%rhs) := do
    -- if cfg.trace_rules then
    --   do rs_strings ← pp_rules rs,
    --     trace ("rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
    -- else skip,

    -- FIXME there is a bit of code duplication because we change the type of
    -- "cfg" when we try a fallback config...
    i ← try_mk_search_instance cfg rs lhs rhs,
    match i with
    | some i := do
      result ← i.search_until_solved,
      handle_search_result cfg rs result
    | none := do
      trace "\nError initialising rewrite_search instance, falling back to emergency config!\n",
      new_cfg ← pure (mk_fallback_config cfg),
      i ← try_mk_search_instance new_cfg rs lhs rhs,
      match i with
      | some i := do
        result ← i.search_until_solved,
        handle_search_result new_cfg rs result
      | none := do
        fail "Could not initialise emergency rewrite_search instance!"
      end
    end
  | _ := fail "target is not an equation"
  end

open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.strategy.edit_distance

meta def default_config : config search_state ed_partial unit := {}
meta def pick_default_config : tactic unit := `[exact tidy.rewrite_search.default_config]

-- TODO coerce {} = ∅ into default_config

end tidy.rewrite_search

namespace tactic.interactive

open tidy.rewrite_search

meta def rewrite_search {α β γ : Type} (rs : parse rw_rules) (cfg : config α β γ . pick_default_config) : tactic string := do
  rs ← rs.rules.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm)),
  do_rewrite_search rs cfg

meta def is_eq_after_binders : expr → bool
  | (expr.pi n bi d b) := is_eq_after_binders b
  | `(%%a = %%b)       := tt
  | _                  := ff

meta def load_exprs : list name → tactic (list expr)
| [] := return []
| (a :: rest) := do
  names ← attribute.get_instances a,
  u ← names.mmap $ mk_const,
  l ← load_exprs rest,
  return (u ++ l)

meta def rewrite_search_using {α β γ : Type} (as : list name) (cfg : config α β γ . pick_default_config) : tactic string := do
  tgt ← target,
  if tgt.has_meta_var then
    fail "rewrite_search is not suitable for goals containing metavariables"
  else skip,
  exprs ← load_exprs as,
  hyps ← local_context,
  hyps ← hyps.mfilter (λ h, (do t ← infer_type h, return ¬ t.has_meta_var)),
  let exprs := exprs ++ hyps,
  --  rules ← close_under_apps exprs, -- TODO don't do this for everything, it's too expensive: only for specially marked lemmas
  let rules := exprs,
  rules ← rules.mfilter $ λ r, (do t ← infer_type r, return (is_eq_after_binders t)),
  let pairs := rules.map (λ e, (e, ff)) ++ rules.map (λ e, (e, tt)),
  do_rewrite_search pairs cfg

end tactic.interactive

meta def search_attribute : user_attribute := {
  name := `search,
  descr := ""
}

run_cmd attribute.register `search_attribute

-- structure cat :=
--   (O : Type)
--   (H : O → O → Type)
--   (i : Π o : O, H o o)
--   (c : Π {X Y Z : O} (f : H X Y) (g : H Y Z), H X Z)
--   (li : Π {X Y : O} (f : H X Y), c (i X) f = f)
--   (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f)
--   (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

-- attribute [search] cat.li cat.a

-- private example (C : cat) (X Y Z : C.O) (f : C.H X Y) (g : C.H Y X) (w : C.c g f = C.i Y) (h k : C.H Y Z) (p : C.c f h = C.c f k) : h = k := 
-- begin
-- rewrite_search_using `search {trace := tt, trace_rules:=tt},
-- end


-- PROJECT cache all_rewrites_list?
