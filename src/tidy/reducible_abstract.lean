-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open interactive
open lean.parser
local postfix `?`:9001 := optional

namespace tactic

private meta def mk_aux_decl_name : option name → tactic name
| none          := new_aux_decl_name
| (some suffix) := do p ← decl_name, return $ p ++ suffix

-- this is the same as `abstract`, but if it is not a proposition we mark it reducible
meta def reducible_abstract (tac : tactic unit) (suffix : option name := none) (zeta_reduce := tt) : tactic unit :=
do fail_if_no_goals,
   gs ← get_goals,
   type ← if zeta_reduce then target >>= zeta else target,
   is_lemma ← is_prop type,
   m ← mk_meta_var type,
   set_goals [m],
   tac,
   n ← num_goals,
   when (n ≠ 0) (fail "abstract tactic failed, there are unsolved goals"),
   set_goals gs,
   val ← instantiate_mvars m,
   val ← if zeta_reduce then zeta val else return val,
   c   ← mk_aux_decl_name suffix,
   e   ← add_aux_decl c type val is_lemma,
   if ¬ is_lemma then 
     set_basic_attribute `reducible c tt
   else
     tactic.skip,
   exact e

namespace interactive

meta def reducible_abstract (id : parse ident?) (tac : itactic) : tactic unit :=
tactic.reducible_abstract tac id

end interactive

end tactic