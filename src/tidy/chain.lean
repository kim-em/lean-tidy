-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .some_goal
import .repeat_at_least_once
import .recover

open tactic

variable {α : Type}

class has_focus (α : Type) :=
(work_on_goal : ℕ → list α → α)

variable (single_goal_tactic : tactic (list α))
variable [has_focus α]

/-
We repeatedly apply `chain_single_goal` to the first goal on which it succeeds.
-/
meta def chain_multiple_goals : tactic (list α) :=
do (p, q) ← repeat_at_least_once (some_goal single_goal_tactic) <|> fail "chain did not find any goal where progress could be made",
   return ((p :: q).map $ λ x, has_focus.work_on_goal x.1 x.2)

variable (abstraction : tactic unit)

meta def chain_single_goal_aux (tactics : list (tactic α)) : tactic (list α) :=
do ng ← num_goals,
   match ng with
   | 0 := fail "no goals left"
   | 1 := first tactics >>= λ a, return [a]
   | _ := chain_multiple_goals single_goal_tactic
   end

private meta def mk_aux_decl_name : option name → tactic name
| none          := new_aux_decl_name
| (some suffix) := do p ← decl_name, return $ p ++ suffix

meta def close_goal_with_declaration (goal : expr) (type : expr) (metavar : expr) (is_lemma : bool) : tactic unit :=
do set_goals [goal],
   val ← instantiate_mvars metavar,
   c   ← mk_aux_decl_name none,
   e   ← add_aux_decl c type val is_lemma,
   if ¬ is_lemma then 
     set_basic_attribute `reducible c tt
   else
     tactic.skip,
   exact e,
   append_goals e.metavariables
/-
This tactic requires that we start with a single goal.
We first make a synthetic copy of the goal, as a new metavariable.

We then follow these steps:
1) If there are no remaining goals, we attempt to make a declaration containing 
   the result for the synthetic goal, and then close the original goal using that, and return. (Like `abstract`.)
2) Check how many goals remain:
2a) If there is just a single goal, attempt to execute a tactic from the list, and if this succeeds return to 1).
2b) If there are multiple goals, run `chain_multiple_goals` 
    (which will recursively call back into this function, making a new synthetic copy of each goal), 
    and if this succeeds return to 1).
3) At this point, we have one or more goals, which we can't make any further progress on.
   Without making any declaration (TODO: should we make a declaration with parameters?), we unify the partial solution we've found to the synthetic goal with the original goal,
   and return.
-/
/-
All this effort pays off --- here's some timing data:

old chain (did not automatically abstract intermediate results)
cumulative profiling times:
	compilation 396ms
	decl post-processing 6.77ms
	elaboration 51.6s
	elaboration: tactic compilation 140ms
	elaboration: tactic execution 16.8s
	parsing 234ms
	type checking 20.5ms

new chain:
cumulative profiling times:
	compilation 377ms
	decl post-processing 7.26ms
	elaboration 14.1s
	elaboration: tactic compilation 135ms
	elaboration: tactic execution 9.57s
	parsing 231ms
	type checking 19.9ms
-/
meta def chain_single_goal (tactics : list (tactic α)) : tactic (list α) :=
do gs ← get_goals,
   guard (gs.length = 1),
   type ← target >>= zeta,
   is_lemma ← is_prop type,
   m ← mk_meta_var type,
   set_goals [m],
   as ← repeat_with_results (chain_single_goal_aux chain_single_goal tactics),
   guard (as.length > 0) <|> fail "chain tactic made no progress",
   ng ← num_goals,
   match ng with
   | 0 := close_goal_with_declaration gs.head type m is_lemma
   | _ := -- We attempt to report our partial answer using unification.
          -- (do r ← instantiate_mvars m,              
          --     unify r gs.head >> trace "via unification") <|>
          -- but sometimes that fails, while exact does the job:
          (do r ← instantiate_mvars m,
              set_goals gs,
              exact r,
              append_goals r.metavariables,
              trace "via exact") <|> fail "Could not close goal using solution to synthetic goal!"
   end,
   return as.join

meta def chain_core (tactics : list (tactic α)) : tactic (list α) := 
do ng ← num_goals,
   match ng with
   | 0 := fail "no goals!"
   | 1 := chain_single_goal tactics
   | _ := chain_multiple_goals (chain_single_goal tactics)
   end

variable [has_to_format α]

meta def trace_output (t : tactic α) : tactic α :=
do r ← t,
   name ← decl_name,
   trace format!"chain successfully applied a tactic during elaboration of {name} with result: {r}",
   pure r

structure chain_cfg := 
( trace_steps        : bool := ff )

private meta def chain_handle_trace (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
if cfg.trace_steps then
  chain_core (tactics.map trace_output)
else 
  chain_core tactics

meta def chain (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
do sequence ← chain_handle_trace cfg tactics,
   guard (sequence.length > 0) <|> fail "chain tactic made no progress",
   pure sequence.reverse

instance : has_focus unit :=
{ work_on_goal := λ _ _, unit.star}

instance : has_focus string :=
{ work_on_goal := λ n ts, 
   "work_on_goal " ++ (to_string n) ++ " {\n  " ++ (",\n  ".intercalate ts) ++ "\n}" }

-- instance has_focus_fallback {α} [inhabited α] : has_focus α :=
-- { work_on_goal := λ _ as, as.head }
