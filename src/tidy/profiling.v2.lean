-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .tidy

open tactic

/-
This is just a minimal instantiation of a profiling framework.
-/

universe variables u v

meta structure profiling_state :=
  ( invocations : nat )
  ( state       : option tactic_state )

meta def profiling_tactic := λ α : Type, tactic (α × profiling_state)

meta instance : monad (profiling_tactic) := {
  pure := λ { α : Type } ( a : α ) ( s: tactic_state ), begin apply result.success, exact (a, ⟨ 0, some tactic.monad.pure a ⟩), exact tactic_state.mk_empty end,
  bind := λ { α β : Type } o f, sorry,
  bind_assoc := sorry,
  pure_bind  := sorry,
  id_map     := sorry
}

meta def count_invocations { α : Type } ( t : tactic α ) : profiling_tactic α :=
λ p, do o ← try_core t,
        match o with
        | (some r) := pure (r, ⟨ p.invocations + 1, ff ⟩)
        | none     := pure (begin admit end, ⟨ p.invocations + 1, tt ⟩)
        end



-- def option_commutor ( m : Type → Type ) [monad m] ( α : Type ) : option (m α) → m (option α)
-- | none     := pure none
-- | (some r) := r >>= (pure ∘ some)

-- def option_commutor' ( m : Type → Type ) [monad m] ( α : Type ) : m (option α) → option (m α) :=
-- begin
--   intros x,
--   apply some,
  
-- end


-- def option_monad ( m : Type → Type ) [monad m] : monad (λ α, option (m α)) := {
--   pure := λ { α : Type } ( a : α ), pure (pure a),
--   bind := λ { α β : Type } o f, begin induction o, exact none, have p := ((option_commutor m β) ∘ f), have x := a >>= p,  end,
--   bind_assoc := sorry,
--   pure_bind  := sorry,
--   id_map     := sorry
-- }


