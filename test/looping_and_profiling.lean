-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.loop_detection
import tidy.profiling

open tactic

namespace tidy.test

meta def interactive_simp := `[simp]

meta instance loop_detecting_and_profiling_coercion { α : Type } : has_coe (interaction_monad tactic_state α) (interaction_monad ((tactic_state × invocation_count) × loop_detection_state) α) :=
⟨ instrument_for_loop_detection ∘ profiling_tactic_coercion.coe ⟩ 

lemma looping_and_profiling_at_the_same_time_test_1 : true :=
begin
profiling $ (detect_looping $ triv),
end

lemma looping_and_profiling_at_the_same_time_test_2 : true :=
begin
success_if_fail { profiling $ detect_looping $ skip >> skip },
triv
end

lemma looping_and_profiling_at_the_same_time_test_3 : 1 = 1 :=
begin
success_if_fail { profiling $ detect_looping $ interactive_simp >> skip >> skip }, -- failed, with 2 successful invocations
simp
end

end tidy.test

