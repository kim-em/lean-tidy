-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .some_goal
import .repeat_at_least_once
import .recover
import .pretty_print
import data.option

open interactive

namespace tactic

/-
This file defines a `chain` tactic, which takes a list of tactics, and exhaustively tries to apply them
to the goals, until no tactic succeeds on any goal.

Along the way, it generates auxiliary declarations, in order to speed up elaboration time
of the resulting (sometimes long!) proofs.

This tactic is used by the `tidy` tactic.
-/

-- α is the return type of our tactics. When `chain` is called by `tidy`, this is string,
-- describing what that tactic did as an interactive tactic.
variable {α : Type}

/-
Because chain sometimes pauses work on the first goal and works on later goals, we need a method
for combining a list of results generated while working on a later goal into a single result.
This enables `tidy {trace_result := tt}` to output faithfully reproduces its operation, e.g.
````
intros,
simp,
apply lemma_1,
work_on_goal 2 {
  dsimp,
  simp
},
refl
````
-/

class has_focus (α : Type) :=
(work_on_goal : ℕ → list α → α)

instance : has_focus unit :=
{ work_on_goal := λ _ _, unit.star}

instance string_has_focus : has_focus string :=
{ work_on_goal := λ n ts, 
  if false /-n = 0-/ then
    ", ".intercalate ts
  else
   "work_on_goal " ++ (to_string n) ++ " {\n  " ++ (",\n  ".intercalate ts) ++ "\n}" }

namespace interactive
open lean.parser
meta def work_on_goal : parse small_nat → itactic → tactic unit
| n t := do goals ← get_goals,
            let earlier_goals := goals.take n,
            let later_goals := goals.drop (n+1),
            set_goals (goals.nth n).to_list,
            t,
            new_goals ← get_goals,
            set_goals (earlier_goals ++ new_goals ++ later_goals)
end interactive

/- 
The chain tactic is built out of two components,
* `chain_multiple_goals`, which tries working on each goal sequentially,
* `chain_single_goal`, which tries out all the 'chained' tactics on a given goal,
  and also performs some magic making declarations for intermediate steps (to speed up elaboration),
  and passing control back to `chain_multiple_goals` when necessary.
-/

variable (single_goal_tactic : tactic (list α)) -- because the two tactics need to call each other, we pass a reference
variable [has_focus α]

/-
The tactic `chain_multiple_goals` repeatedly applies `chain_single_goal` to the first goal on which it succeeds.
-/
meta def chain_multiple_goals : tactic (list α) :=
do (p, q) ← repeat_at_least_once (some_goal single_goal_tactic) <|> fail "chain did not find any goal where progress could be made",
   return ((p :: q).reverse.map $ λ x, has_focus.work_on_goal x.1 x.2.reverse)

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

meta def close_goal_with_declaration (goal : expr) (type : expr) (metavar : expr) : tactic unit :=
do set_goals [goal],
   val ← instantiate_mvars metavar,
   c   ← mk_aux_decl_name none,
   is_lemma ← is_prop type,
   e   ← add_aux_decl c type val is_lemma,
  --  if ¬ is_lemma then 
  --    set_basic_attribute `reducible c tt
  --  else
  --    tactic.skip,
   exact e,
   append_goals e.metavariables

/-
`chain_single_goal` requires that we start with a single goal.
We first make a synthetic copy of the goal, as a new metavariable.

We then follow these steps:
1. If there are no remaining goals, we attempt to make a declaration containing 
   the result for the synthetic goal, and then close the original goal using that, and return. (Like `abstract`.)
2. Check how many goals remain:
2.a. If there is just a single goal, attempt to execute a tactic from the list, and if this succeeds return to 1.
2.b. If there are multiple goals, run `chain_multiple_goals` 
    (which will recursively call back into this function, making a new synthetic copy of each goal), 
    and if this succeeds return to 1.
3. At this point, we have one or more goals, which we can't make any further progress on.
   Without making any declaration, we use exact (which is more robust than unify) 
   to substitute the partial solution we've found to the synthetic goal into the original goal,
   and return.
-/

meta def chain_single_goal (make_declarations : bool) (tactics : list (tactic α)) : tactic (list α) :=
do gs ← get_goals,
   guard (gs.length = 1),
   if make_declarations then
     do type ← target >>= zeta,
        m ← mk_meta_var type,
        set_goals [m],
        as ← repeat_with_results (chain_single_goal_aux chain_single_goal tactics),
        guard (as.length > 0) <|> fail "chain tactic made no progress",
        ng ← num_goals,
        match (ng, bnot type.has_meta_var) with
        | (0, tt) := close_goal_with_declaration gs.head type m
        | _       := (do r ← instantiate_mvars m,
                          set_goals gs,
                          exact r,
                          append_goals r.metavariables) <|> fail "bug: could not close goal using solution to synthetic goal!"
        end,
        return as.reverse.join
    else
      do as ← repeat_with_results (chain_single_goal_aux chain_single_goal tactics),
         guard (as.length > 0) <|> fail "chain tactic made no progress",
         return as.reverse.join


structure chain_cfg := 
(trace_steps        : bool := ff)
(make_declarations  : bool := tt)

meta def chain_core (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) := 
do ng ← num_goals,
   let tac := chain_single_goal cfg.make_declarations tactics,
   match ng with
   | 0 := fail "no goals left"
   | 1 := tac
   | _ := chain_multiple_goals tac
   end

variable [has_to_format α]

meta def trace_output (t : tactic α) : tactic α :=
do tgt ← target,
   r ← t,
   name ← decl_name,
   trace format!"chain successfully applied a tactic during elaboration of {name}:",
   tgt ← pretty_print tgt,
   trace format!"old target: {tgt}",
   gs ← get_goals,
   gs' ← gs.mmap (λ g, infer_type g >>= pretty_print),
   trace gs',
   mvars ← metavariables,
   mvars' ← mvars.mmap (λ g, infer_type g >>= pretty_print),
   trace mvars',
   trace format!"tactic:     {r}",
   tgt ← try_core target,
   tgt ← match tgt with
          | (some tgt) := do pretty_print tgt
          | none       := do return "′no goals′"
          end,
   trace format!"new target: {tgt}",
   gs ← get_goals,
   gs' ← gs.mmap (λ g, infer_type g >>= pretty_print),
   trace gs',
   mvars ← metavariables,
   mvars' ← mvars.mmap (λ g, infer_type g >>= pretty_print),
   trace mvars',
   pure r

private meta def chain_handle_trace (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
if cfg.trace_steps then
  chain_core cfg (tactics.map trace_output)
else 
  chain_core cfg tactics

meta def chain (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
do sequence ← chain_handle_trace cfg tactics,
   guard (sequence.length > 0) <|> fail "chain tactic made no progress",
   pure sequence.reverse

end tactic