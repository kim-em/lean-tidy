-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .pempty
import .at_least_one 
import .pretty_print

open tactic

meta def automatic_induction_at (h : expr) : tactic string :=
do
t' ← infer_type h,
t' ← whnf t',
let use_cases := match t' with
| `(unit)      := tt
| `(punit)     := tt
| `(false)     := tt
| `(empty)     := tt
| `(pempty)    := tt
| `(ulift _)   := tt
| `(plift _)   := tt
| `(prod _ _)  := tt
| `(and _ _)   := tt
| `(sigma _)   := tt
| `(subtype _) := tt
| `(Exists _)  := tt
| `(fin 0)     := tt
| _            := ff
end,
if use_cases then
  do cases h, pp ← pretty_print h, return ("cases " ++ pp)
else
  match t' with
  | `(eq _ _)        := do induction h, pp ← pretty_print h, return ("induction " ++ pp)
  | `(quot _)        := do induction h, pp ← pretty_print h, return ("induction " ++ pp)
  | _                := failed
  end

meta def automatic_induction : tactic string :=
do l ← local_context,
   results ← at_least_one (l.reverse.map(λ h, automatic_induction_at h)),
   return (string.intercalate ", " results)