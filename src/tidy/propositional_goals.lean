-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

private meta def propositional_goals_core { α : Type } (tac : tactic α) : list expr → list expr →  (list (option α)) → bool → tactic (list (option α))
| []        ac results progress := guard progress >> set_goals ac >> pure results
| (g :: gs) ac results progress :=
  do t ← infer_type g,
     p ← is_prop t,
     if p then do {
        set_goals [g],
        succeeded ← try_core tac,
        new_gs    ← get_goals,
        propositional_goals_core gs (ac ++ new_gs) (succeeded :: results ) (succeeded.is_some || progress)
     } else do {
       propositional_goals_core gs (ac ++ [ g ]) (none :: results) progress
     }

/-- Apply the given tactic to any propositional goal where it succeeds. The tactic succeeds only if
   tac succeeds for at least one goal. -/
meta def propositional_goals { α : Type } ( t : tactic α ) : tactic (list (option α)) :=
do gs ← get_goals,
   results ← propositional_goals_core t gs [] [] ff,
   pure results.reverse
