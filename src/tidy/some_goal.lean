-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

variable {α : Type}

meta def prepend_goal (g : expr) : tactic unit :=
do goals ← get_goals,
   set_goals (g :: goals)

meta def append_goals (gs : list expr) : tactic unit :=
do goals ← get_goals,
   set_goals (goals ++ gs)

meta def some_goal_aux (t : tactic α) : ℕ → list expr → tactic (ℕ × α)
| n (g :: gs) := do set_goals [g],
                    o ← try_core t,
                    match o with
                    | none     := do r ← some_goal_aux (n+1) gs, prepend_goal g, return r
                    | (some r) := do append_goals gs, return (n, r)
                    end
| _ []        := fail "some_goal did not find a goal the tactic could succeed on"

/- Finds a goal on which the tactic `t` succeeds.
   If there is one, returns the index of the goal, along with the result of the tactic.
   Otherwise, fails. -/
meta def some_goal (t : tactic α) : tactic (ℕ × α) :=
do goals ← get_goals,
   some_goal_aux t 0 goals