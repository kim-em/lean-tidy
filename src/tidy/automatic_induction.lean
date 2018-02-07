-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .at_least_one 

open tactic


meta def induction_at (e :expr) := tactic.interactive.induction (none, to_pexpr e) none [] none

-- definition foo (f : ite (_0 = _0) punit pempty) : punit.star = f := begin
-- induction f,
-- refl,
-- end

meta def induction_only : tactic unit :=
do l ← local_context,
   match l with 
   | [e] := do t ← infer_type e,
               t ← whnf t,
               match t with
               | `(punit) := induction' e
               | _ := skip
               end
   | _   := failed
   end

definition foo' (f : ite (_0 = _0) punit pempty) : punit.star = f :=
begin
induction_only,
refl
end


meta def automatic_induction_at (h : expr) : tactic unit :=
do t' ← infer_type h,
   t ← whnf t',
match t with
| `(unit)      := induction h >> skip
| `(punit)     := induction h >> skip
| `(false)     := induction h >> skip
| `(empty)     := induction h >> skip
| `(fin nat.zero) := induction h >> `[cases is_lt]
| `(ulift _)   := induction h >> skip
| `(plift _)   := induction h >> skip
| `(eq _ _)    := induction h >> skip
| `(prod _ _)  := induction h >> skip
| `(and _ _)   := induction h >> skip
| `(sigma _)   := induction h >> skip
| `(subtype _) := induction h >> skip
| _              := failed
end

meta def automatic_induction : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map(λ h, automatic_induction_at h))