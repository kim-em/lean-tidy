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