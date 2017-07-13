-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..loop_detection
import ..profiling

open tactic

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
success_if_fail { profiling $ detect_looping $ simp >> skip >> skip }, -- failed, with 2 invocations
simp
end
