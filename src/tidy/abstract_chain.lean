import .chain
import .repeat_at_least_once
import .recover
import .fsplit

open tactic

inductive tactic_descriptor (α : Type)
| skip {} : tactic_descriptor
| and_then (a : α) (t : tactic_descriptor) : tactic_descriptor
| focus (n : ℕ) (t : tactic_descriptor) : tactic_descriptor

variable {α : Type}

class has_focus (α : Type) :=
(work_on_goal : ℕ → list α → α)

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

variable (single_goal_tactic : tactic (list α))
variable [has_focus α]

/-
We repeatedly apply `abstract_chain_single_goal` to the first goal on which it succeeds.
-/
meta def abstract_chain_multiple_goals : tactic (list α) :=
do (p, q) ← repeat_at_least_once (some_goal single_goal_tactic),
   return ((p :: q).map $ λ x, has_focus.work_on_goal x.1 x.2)

variable (abstraction : tactic unit)

meta def abstract_chain_single_goal_aux (tactics : list (tactic α)) : tactic (list α) :=
do ng ← num_goals,
   match ng with
   | 0 := fail "no goals left"
   | 1 := first tactics >>= λ a, return [a]
   | _ := abstract_chain_multiple_goals single_goal_tactic
   end

private meta def mk_aux_decl_name : option name → tactic name
| none          := new_aux_decl_name
| (some suffix) := do p ← decl_name, return $ p ++ suffix

meta def close_goal_with_declaration (goal : expr) (type : expr) (metavar : expr) (is_lemma : bool) : tactic unit :=
do set_goals [goal],
   val ← instantiate_mvars metavar >>= zeta,
   c   ← mk_aux_decl_name none,
   e   ← add_aux_decl c type val is_lemma,
   trace format!"closing goal using {e}",
   if ¬ is_lemma then 
     set_basic_attribute `reducible c tt
   else
     tactic.skip,
   exact e
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
meta def abstract_chain_single_goal (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
do gs ← get_goals,
   guard (gs.length = 1),
   type ← target >>= zeta,
   is_lemma ← is_prop type,
   m ← mk_meta_var type,
   set_goals [m],
   as ← repeat_with_results (abstract_chain_single_goal_aux abstract_chain_single_goal tactics),
   guard (as.length > 0),
   ng ← num_goals,
   match ng with
   | 0 := close_goal_with_declaration gs.head type m is_lemma
   | _ := do r ← instantiate_mvars m,
             unify r gs.head
   end,
   result >>= trace,
   return as.join

meta def abstract_chain_core (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) := 
do ng ← num_goals,
   match ng with
   | 0 := fail "no goals!"
   | 1 := abstract_chain_single_goal cfg tactics
   | _ := abstract_chain_multiple_goals (abstract_chain_single_goal cfg tactics)
   end

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

instance : has_focus unit :=
{ work_on_goal := λ _ _, unit.star}

def F : 1 = 1 ∧ 2 = 2:=
begin
  abstract_chain {trace_steps:=tt} [`[refl], `[split]],
end

#print F
#print F._aux_3

def G : ℕ × ℕ :=
begin
  abstract_chain {trace_steps:=tt} [`[split]],
  abstract_chain {trace_steps:=tt} [`[exact 0]],
end

#print G
#print G._aux_1

open tactic

structure C :=
(a : ℕ)
(b : a > 0)
(c : array a ℕ)

def H : C :=
begin
abstract foo { split, rotate 2, exact 1, abstract { exact dec_trivial }, split, abstract bar { intros, exact 0 } }
end

set_option pp.proofs true
#print H   -- theorem H : C := {a := 1, b := of_as_true trivial, c := {data := λ (i : fin 1), 0}}
#print H.foo -- 'unknown identifier foo'
#print H.bar -- 'unknown identifier bar'