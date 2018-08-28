-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mario Carneiro, Scott Morrison

open tactic

-- This has been PR'd to mathlib; remove when it's merged.
-- https://github.com/leanprover/mathlib/pull/125

meta def expr.metavariables (r : expr) : list expr := 
r.fold [] $ λ e _ l,
  match e with
  | expr.mvar _ _ _ := insert e l
  | _ := l
  end

meta def metavariables : tactic (list expr) :=
do r ← result,
   pure r.metavariables

meta def propositional_goal : tactic unit :=
do g :: _ ← get_goals,
   ty ← infer_type g,
   p ← is_prop ty,
   guard p

meta def subsingleton_goal : tactic unit :=
do g :: _ ← get_goals,
   ty ← infer_type g >>= instantiate_mvars,
   to_expr ``(subsingleton %%ty) >>= mk_instance >> skip

meta def terminal_goal : tactic unit :=
propositional_goal <|> subsingleton_goal <|>
do g :: gs ← get_goals,
   gs.mmap' $ λ g, (do t ← infer_type g, t ← instantiate_mvars t, d ← kdepends_on t g,
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
