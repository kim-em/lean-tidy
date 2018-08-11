-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .mk_apps
import .pretty_print

open tactic

meta def forwards_attribute : user_attribute := {
  name := `forwards,
  descr := "A lemma whose conclusion should be deduced whenever all arguments are satisfiable from hypotheses; use `forwards_reasoning` to automatically try all lemmas tagged `@[forwards]`."
}

run_cmd attribute.register `forwards_attribute

meta def guard_no_duplicate_hypothesis (t : expr) : tactic unit :=
do hyps ← local_context,
   types ← hyps.mmap (λ h, infer_type h),
   if types.mem t then failed else skip

meta def attempt_forwards_reasoning : list expr → tactic string
| [] := fail "forwards_reasoning failed"
| (e :: es) := do
    t ← infer_type e,
    if t.is_pi then
      do hyps ← local_context,
         apps ← mk_apps e hyps,
         attempt_forwards_reasoning (apps ++ es)
    else (do guard_no_duplicate_hypothesis t,
             n ← mk_fresh_name,
             assertv n t e,
             t_pp ← pretty_print t,
             e_pp ← pretty_print e,
             return ("have " ++ (n.to_string_with_sep "_") ++ " : " ++ t_pp ++ " := " ++ e_pp)) <|> attempt_forwards_reasoning es

/-- Try to deduce any lemma marked with the attribute @[forwards] -/
meta def forwards_reasoning : tactic string :=
do cs ← attribute.get_instances `forwards,
   es ← cs.mmap mk_const,
   attempt_forwards_reasoning es