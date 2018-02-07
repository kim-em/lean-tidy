-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

-- all of this is just copypasta from interactive.lean, with the exception of the line
-- change_core new_h_type (some h) <|>

-- FIXME make a PR?

open tactic
open interactive
open interactive.types
open tactic.interactive
open lean.parser
local postfix `?`:9001 := optional

namespace tactic.interactive

meta def change_core (e : expr) : option expr → tactic unit
| none     := tactic.change e
| (some h) :=
  do num_reverted : ℕ ← tactic.revert h,
     expr.pi n bi d b ← target,
     tactic.change $ expr.pi n bi e b,
     intron num_reverted

meta def simp_core_aux' (cfg : simp_config) (discharger : tactic unit) (s : simp_lemmas) (u : list name) (hs : list expr) (tgt : bool) : tactic unit :=
do to_remove ← hs.mfilter $ λ h, do {
         h_type ← infer_type h,
         (do (new_h_type, pr) ← simplify s u h_type cfg `eq discharger,
             change_core new_h_type (some h) <|>
             (do assert h.local_pp_name new_h_type,
                 mk_eq_mp pr h >>= tactic.exact))  >> return tt
         <|>
         (return ff) },
   goal_simplified ← if tgt then (simp_target s u cfg discharger >> return tt) <|> (return ff) else return ff,
   guard (cfg.fail_if_unchanged = ff ∨ to_remove.length > 0 ∨ goal_simplified) <|> fail "simplify tactic failed to simplify",
   to_remove.mmap' (λ h, tactic.interactive.try (tactic.clear h))

meta def simp_core' (cfg : simp_config) (discharger : tactic unit)
                   (no_dflt : bool) (hs : list simp_arg_type) (attr_names : list name)
                   (locat : loc) : tactic unit :=
match locat with
| loc.wildcard := do (all_hyps, s, u) ← mk_simp_set_core no_dflt attr_names hs tt,
                     if all_hyps then tactic.simp_all s u cfg discharger
                     else do hyps ← non_dep_prop_hyps, simp_core_aux' cfg discharger s u hyps tt
| _            := do (s, u) ← mk_simp_set no_dflt attr_names hs,
                     ns ← locat.get_locals,
                     simp_core_aux' cfg discharger s u ns locat.include_goal
end
>> tactic.interactive.try tactic.triv >> tactic.interactive.try (tactic.reflexivity reducible)

/--
The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses. It has many variants.

`simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.

`simp [h₁ h₂ ... hₙ]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions. If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with `f` are used. This provides a convenient way to unfold `f`.

`simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.

`simp *` is a shorthand for `simp [*]`.

`simp only [h₁ h₂ ... hₙ]` is like `simp [h₁ h₂ ... hₙ]` but does not use `[simp]` lemmas

`simp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`, but removes the ones named `idᵢ`.

`simp at h₁ h₂ ... hₙ` simplifies the non-dependent hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. The tactic fails if the target or another hypothesis depends on one of them. The token `⊢` or `|-` can be added to the list to include the target.

`simp at *` simplifies all the hypotheses and the target.

`simp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.

`simp with attr₁ ... attrₙ` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr₁]`, ..., `[attrₙ]` or `[simp]`.
-/
meta def simp' (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
let cfg := if use_iota_eqn.is_none then cfg else {iota_eqn := tt, ..cfg} in
propagate_tags (simp_core' cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat)

end tactic.interactive

-- FIXME: see as https://github.com/leanprover/lean/issues/1915
-- unfortunately this one often fails to replace hypotheses, when the goal depends on them.
meta def simp_at_each : tactic unit :=
do l ← tactic.local_context,
  (s, u) ← tactic.mk_simp_set ff [] [],
  tactic.interactive.simp_core_aux' {} tactic.failed s u l ff


-- Can we give a more direct proof??
private def foo ( f : if tt = ff then empty else unit ) : unit.star = f :=
begin
-- induction f,
-- refl
simp_at_each,
induction f,
refl
end