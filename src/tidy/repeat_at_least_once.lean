-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

namespace tactic

variable {α : Type}

private meta def repeat'' (t : tactic α) : list α → tactic (list α)
| L := do r ← t | return L.reverse,
          repeat'' (r :: L)

private meta def repeat' (t : tactic α) : tactic (list α) := repeat'' t []

meta def repeat_at_least_once ( t : tactic α ) : tactic (α × list α) :=
do r ← t,
   L ← repeat' t,
   return (r, L)

run_cmd add_interactive [`repeat_at_least_once]

end tactic