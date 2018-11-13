import .options
import .string

open tactic

meta def pretty_print (e : expr) (implicits : bool := ff) (full_cnsts := ff) : tactic string :=
do options ← get_options,
   set_options $ options.set_list_bool [
     (`pp.notation, true),
     (`pp.universes, false),
     (`pp.implicit, implicits),
     (`pp.structure_instances, ¬full_cnsts)
   ],
   t ← pp e,
   set_options options,
   pure t.to_string

/-

  pp.coercions (Bool) (pretty printer) display coercionss (default: true)
  pp.structure_projections (Bool) (pretty printer) display structure projections using field notation (default: true)
  pp.locals_full_names (Bool) (pretty printer) show full names of locals (default: false)
  pp.annotations (Bool) (pretty printer) display internal annotations (for debugging purposes only) (default: false)
  pp.hide_comp_irrelevant (Bool) (pretty printer) hide terms marked as computationally irrelevant, these marks are introduced by the code generator (default: true)
  pp.unicode (Bool) (pretty printer) use unicode characters (default: true)
  pp.colors (Bool) (pretty printer) use colors (default: false)
  pp.structure_instances (Bool) (pretty printer) display structure instances using the '{ field_name := field_value, ... }' notation or '⟨field_value, ... ⟩' if structure is tagged with [pp_using_anonymous_constructor] attribute (default: true)
  pp.purify_metavars (Bool) (pretty printer) rename internal metavariable names (with "user-friendly" ones) before pretty printing (default: true)
  pp.max_depth (Unsigned Int) (pretty printer) maximum expression depth, after that it will use ellipsis (default: 64)
  pp.notation (Bool) (pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters) (default: true)
  pp.preterm (Bool) (pretty printer) assume the term is a preterm (i.e., a term before elaboration) (default: false)
  pp.implicit (Bool) (pretty printer) display implicit parameters (default: false)
  pp.goal.max_hypotheses (Unsigned Int) (pretty printer) maximum number of hypotheses to be displayed (default: 200)
  pp.private_names (Bool) (pretty printer) display internal names assigned to private declarations (default: false)
  pp.goal.compact (Bool) (pretty printer) try to display goal in a single line when possible (default: false)
  pp.universes (Bool) (pretty printer) display universes (default: false)
  pp.full_names (Bool) (pretty printer) display fully qualified names (default: false)
  pp.purify_locals (Bool) (pretty printer) rename local names to avoid name capture, before pretty printing (default: true)
  pp.strings (Bool) (pretty printer) pretty print string and character literals (default: true)
  pp.all (Bool) (pretty printer) display coercions, implicit parameters, proof terms, fully qualified names, universes, and   pp.beta (Bool) (pretty printer) apply beta-reduction when pretty printing (default: false)
  pp.max_steps (Unsigned Int) (pretty printer) maximum number of visited expressions, after that it will use ellipsis (default: 5000)
  pp.width (Unsigned Int) (pretty printer) line width (default: 120)
  pp.proofs (Bool) (pretty printer) if set to false, the type will be displayed instead of the value for every proof appearing as an argument to a function (default: true)
  pp.numerals (Bool) (pretty printer) display nat/num numerals in decimal notation (default: true)
  pp.delayed_abstraction (Bool) (pretty printer) display the location of delayed-abstractions (for debugging purposes) (default: true)
  pp.instantiate_mvars (Bool) (pretty printer) instantiate assigned metavariables before pretty printing terms and goals (default: true)
  pp.structure_instances_qualifier (Bool) (pretty printer) include qualifier 'struct_name .' when displaying structure instances using the '{ struct_name . field_name := field_value, ... }' notation, this option is ignored when pp.structure_instances is false (default: false)
  pp.use_holes (Bool) (pretty printer) use holes '{! !}' when pretty printing metavariables and `sorry` (default: false)
  pp.indent (Unsigned Int) (pretty printer) default indentation (default: 2)
  pp.binder_types (Bool) (pretty printer) display types of lambda and Pi parameters (default: true)

-/
