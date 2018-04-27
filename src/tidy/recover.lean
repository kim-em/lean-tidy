-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mario Carneiro, Scott Morrison

open tactic

meta def metavariables : tactic (list expr) :=
do r ← result,
   pure (r.fold [] $ λ e _ l,
     match e with
     | expr.mvar _ _ _ := insert e l
     | _ := l
     end)

meta def terminal_goal : tactic unit :=
  do goals ← get_goals,
     let current_goal := goals.head,
     other_goals ← metavariables,
     let other_goals := other_goals.erase current_goal,
     other_goals.mmap' $ λ g, (do t ← infer_type g, d ← kdepends_on t current_goal,
                                  monad.whenb d $ pp t >>= λ s, fail ("This is not a terminal goal: " ++ s.to_string ++ " depends on it."))

-- meta def terminal_goal : tactic unit :=
-- do g :: gs ← get_goals,
--    gs.for_each $ λ g', guard (¬ g.occurs g')

meta def done_no_metavariables : tactic unit :=
do done,
   mvars ← metavariables,
   guard mvars.empty

meta def recover : tactic unit :=
  do mvars ← metavariables,
     done,
     guard ¬ mvars.empty,
     trace "recovering meta-variables in result!"
     set_goals mvars
