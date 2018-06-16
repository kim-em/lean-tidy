import .chain
import .repeat_at_least_once

open tactic

variable {α : Type}

-- meta def focus_i (i : nat) (t : tactic α) : tactic α :=
-- do goals ← get_goals,
--    earlier_goals ← return (goals.take i),
--    later_goals ← return (goals.drop (i+1)),
--    some goal ← return (goals.nth i),
--    set_goals [goal],
--    r ← t,
--    new_goals ← get_goals,
--    set_goals (earlier_goals ++ new_goals ++ later_goals),
--    pure r

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

/-
We repeatedly apply `abstract_chain_single_goal` to the first goal on which it succeeds.
-/
meta def abstract_chain_multiple_goals (cfg : chain_cfg) (single_goal_tactic : list (tactic α) → tactic (list α)) (tactics : list (tactic α)) : tactic (list (ℕ × α)) :=
do r ← repeat_at_least_once (some_goal (single_goal_tactic tactics)),
   -- FIXME work out return values
   return []
    

/-
This tactic requires that we start with a single goal.
We first make a synthetic copy of the goal, as a new metavariable.

We then follow these steps:
1) If there are no remaining goals, we attempt to make a declaration containing 
   the result for the synthetic goal, and then close the original goal using that, and return. (Like `abstract`.)
2) Check how many goals remain:
2a) If there is just a single goal, attempt to execute a tactic from the list, and if this succeeds return to 1).
2b) If there are multiple goals, run `abstract_chain_multiple_goals`, and if this succeeds return to 1).
3) At this point, we have one or more goals, which we can't make any further progress on.
   Without making any declaration (?), we unify the partial solution we've found to the synthetic goal with the original goal,
   and return.
-/
meta def abstract_chain_single_goal (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) := sorry


/-
-- We begin with some list of goals.
-- 
-/
meta def abstract_chain_core (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) := sorry

variable [has_to_format α]

private meta def abstract_chain_handle_trace (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
if cfg.trace_steps then
  abstract_chain_core cfg (tactics.map trace_output)
else 
  abstract_chain_core cfg tactics

meta def abstract_chain (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
do sequence ← abstract_chain_handle_trace cfg tactics,
   guard (sequence.length > 0) <|> fail "chain tactic made no progress",
   pure sequence.reverse