-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .at_least_one 

open tactic

inductive {u} pempty : Type u

-- FIXME this is somehow too aggressive?
-- meta def induction_at (e :expr) := tactic.interactive.induction (none, to_pexpr e) none [] none

meta def automatic_induction_at (h : expr) : tactic unit :=
do t' ← infer_type h,
--    t ← whnf t',
match t' with
| `(unit)      := cases h >> skip
| `(punit)     := cases h >> skip
| `(false)     := cases h >> skip
| `(empty)     := cases h >> skip
| `(pempty)    := cases h >> skip
| `(ulift _)   := cases h >> skip
| `(plift _)   := cases h >> skip
| `(eq _ _)    := induction h >> skip  -- cases here triggers https://github.com/leanprover/lean/issues/1942
| `(prod _ _)  := cases h >> skip
| `(and _ _)   := cases h >> skip
| `(sigma _)   := cases h >> skip
| `(subtype _) := cases h >> skip
| `(Exists _)  := cases h >> skip
| `(fin nat.zero) := cases h >> `[cases is_lt]
| _              := failed
end

meta def automatic_induction : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map(λ h, automatic_induction_at h))