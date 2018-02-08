-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mario Carneiro

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
     current_goal ← pure goals.head,
     other_goals ← metavariables,
     other_goals ← pure (other_goals.erase current_goal),
     types ← other_goals.mmap $ λ g, infer_type g,
     depends_on ← types.mmap $ λ t, (do
                                       d ← kdepends_on t current_goal,
                                       guard ¬ d <|> fail ("This is not a terminal goal; " ++ t.to_string ++ " depends on it."),
                                       skip),
     skip

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
