-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .at_least_one 

open tactic

inductive {u} pempty : Type u

meta def induction_at (e :expr) := tactic.interactive.induction (none, to_pexpr e) none [] none

meta def automatic_induction_at (h : expr) : tactic unit :=
do t' ← infer_type h,
   t ← whnf t',
match t with
| `(unit)      := induction_at h
| `(punit)     := induction_at h
| `(false)     := induction_at h
| `(empty)     := induction_at h
| `(pempty)    := induction_at h
| `(ulift _)   := induction_at h
| `(plift _)   := induction_at h
| `(eq _ _)    := induction_at h
| `(prod _ _)  := induction_at h
| `(and _ _)   := induction_at h
| `(sigma _)   := induction_at h
| `(subtype _) := induction_at h
| `(fin nat.zero) := induction_at h >> `[cases is_lt]
| _              := failed
end

meta def automatic_induction : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map(λ h, automatic_induction_at h))