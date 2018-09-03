-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .mk_apps
import .pretty_print

open tactic

meta def forward_attribute : user_attribute := {
  name := `forward,
  descr := "A lemma whose conclusion should be deduced whenever all arguments are satisfiable from hypotheses; use `forwards_reasoning` to automatically try all lemmas tagged `@[forward]`."
}

run_cmd attribute.register `forward_attribute

meta def guard_no_duplicate_hypothesis (t : expr) : tactic unit :=
do hyps ← local_context,
   types ← hyps.mmap (λ h, infer_type h),
   success_if_fail (types.mfirst (λ s, is_def_eq s t))

meta def guard_prop (e : expr) : tactic unit :=
do t ← infer_type e,
   guard (t = `(Prop))

meta def attempt_forwards_reasoning (only_props : bool) (s : simp_lemmas) : list (expr × list string) → tactic string
| [] := fail "forwards_reasoning failed"
| (e :: es) := do
    t ← infer_type e.1,
    t' ← try_core (s.dsimplify [] t), -- FIXME too expensive
    let changed := t'.is_some,
    let t := t'.get_or_else t,
    if t.is_pi then
      do hyps ← local_context,
         apps ← mk_apps e.1 hyps,
         apps ← apps.mmap (λ p, do h_pp ← pretty_print p.2, return (p.1, list.cons h_pp e.2)),
         attempt_forwards_reasoning (apps ++ es)
    else (do if only_props then guard_prop t else skip,
             guard_no_duplicate_hypothesis t,
             let n := "_".intercalate e.2.reverse,
             assertv n t e.1,
             term ← pretty_print e.1,
             -- TODO sometimes this reported tactic won't work, and we need to write instead
             -- `have n : t := by convert term`
             return ("have " ++ n ++ " := " ++ term)
             ) <|> attempt_forwards_reasoning es

/-- Attempt to `have` a lemma marked with the attribute @[forward], whose conclusion is not yet known and whose arguments can be filled in by hypotheses. -/
meta def forwards_library_reasoning : tactic string :=
do cs ← attribute.get_instances `forward,
   es ← cs.mmap (λ n, (do e ← mk_const n, let s := n.components.ilast.to_string, return (e, [s]))),
   s ← mk_simp_set ff [] [],
   attempt_forwards_reasoning ff s.1 es

/-- Attempt to `have` a result obtained by applying one hypothesis to others, as long as the conclusion is propositional, is not yet known, and has no further arguments. -/
meta def forwards_reasoning : tactic string :=
do hyps ← local_context,
   es ← hyps.mmap (λ e, (do s ← pretty_print e, return (e, [s]))),
   s ← mk_simp_set ff [] [],
   attempt_forwards_reasoning tt s.1 es

attribute [forward] congr_fun