-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mario Carneiro, Scott Morrison
import tactic.basic

open tactic

meta def subsingleton_goal : tactic unit :=
do g :: _ ← get_goals,
   ty ← infer_type g >>= instantiate_mvars,
   to_expr ``(subsingleton %%ty) >>= mk_instance >> skip

meta def terminal_goal : tactic unit :=
propositional_goal <|> subsingleton_goal <|>
do g :: gs ← get_goals,
   gs.mmap' $ λ g', (do t ← infer_type g', t ← instantiate_mvars t, d ← kdepends_on t g,
                                monad.whenb d $ pp t >>= λ s, fail ("This is not a terminal goal: " ++ s.to_string ++ " depends on it."))

meta def done_no_metavariables : tactic unit :=
do done,
   mvars ← metavariables,
   guard mvars.empty

meta def recover' : tactic unit :=
  do mvars ← metavariables,
     done,
     guard ¬ mvars.empty,
     trace "recovering meta-variables in result!"
     set_goals mvars
