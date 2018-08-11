-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

namespace tactic

variable {α : Type}

private meta def repeat_with_results_aux (t : tactic α) : list α → tactic (list α)
| L := do r ← try_core t,
          match r with
          | none := return L
          | (some r) := repeat_with_results_aux (r :: L)
          end

meta def repeat_with_results (t : tactic α) : tactic (list α) := 
do l ← repeat_with_results_aux t [],
   return l.reverse

meta def repeat_at_least_once (t : tactic α) : tactic (α × list α) :=
do r ← t | fail "repeat_at_least_once failed: tactic did not succeed",
   L ← repeat_with_results t,
   return (r, L)

run_cmd add_interactive [`repeat_at_least_once]

end tactic