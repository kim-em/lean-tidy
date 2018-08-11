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
   success_if_fail (types.mfirst (λ s, is_def_eq s t))
  --  if types.many t then failed else skip

meta def guard_prop (e : expr) : tactic unit :=
do t ← infer_type e,
   guard (t = `(Prop))

meta def attempt_forwards_reasoning (only_props : bool) (s : simp_lemmas) : list expr → tactic string
| [] := fail "forwards_reasoning failed"
| (e :: es) := do
    t ← infer_type e,
    t' ← try_core (s.dsimplify [] t),
    let changed := t'.is_some,
    let t := t'.get_or_else t,
    if t.is_pi then
      do hyps ← local_context,
         apps ← mk_apps e hyps,
         attempt_forwards_reasoning (apps ++ es)
    else (do if only_props then guard_prop t else skip,
             guard_no_duplicate_hypothesis t,
             --  n ← mk_fresh_name,
             let n := `this,
             assertv n t e,
            --  type ← pretty_print t,
             term ← pretty_print e,
            --  if changed then 
            --    return ("have " ++ (n.to_string_with_sep "_") ++ " : " ++ type ++ " := by convert (" ++ term ++ ")")               
            --  else
            --    return ("have " ++ (n.to_string_with_sep "_") ++ " : " ++ type ++ " := " ++ term)
             return ("have := " ++ term)
             ) <|> attempt_forwards_reasoning es

/-- Try to deduce any lemma marked with the attribute @[forwards] -/
meta def forwards_library_reasoning : tactic string :=
do cs ← attribute.get_instances `forwards,
   es ← cs.mmap mk_const,
   s ← mk_simp_set ff [] [],
   attempt_forwards_reasoning ff s.1 es

meta def forwards_reasoning : tactic string :=
do hyps ← local_context,
   s ← mk_simp_set ff [] [],
   attempt_forwards_reasoning tt s.1 hyps   