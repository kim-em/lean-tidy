-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

/- Return target after instantiating metavars and whnf -/
private meta def target' : tactic expr :=
target >>= instantiate_mvars >>= whnf

meta def fsplit : tactic unit :=
do [c] ← target' >>= get_constructors_for | tactic.fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= λ e, apply e {new_goals := new_goals.all, auto_param := tt} >> skip