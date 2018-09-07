import tactic.ring
import tidy.rewrite_search

open tidy.rewrite_search.metric
open tidy.rewrite_search.strategy
open tidy.rewrite_search.tracer

namespace tidy.rewrite_search.vs_ring

constants a b c d e : ℚ

lemma test3 : (a * (b + c)) * d = a * (b * d) + a * (c * d) :=
by rewrite_search [add_comm, add_assoc, mul_assoc, /-mul_comm,-/ left_distrib, right_distrib] {trace_result := tt, trace_summary := tt, /-view := visualiser,-/ metric := edit_distance}

lemma test4 : (a * (b + c + 1)) * d = a * (b * d) + a * (1 * d) + a * (c * d) :=
by rewrite_search [add_comm, add_assoc, mul_one, mul_assoc, /-mul_comm,-/ left_distrib, right_distrib] {trace_result := tt, trace_summary := tt, /-view := visualiser,-/ metric := edit_distance {refresh_freq := 3} weight.cm, strategy := pexplore, max_iterations := 100}

lemma test4_ring : (a * (b + c + 1)) * d = a * (b * d) + a * (1 * d) + a * (c * d) :=
by ring

lemma test5 : (a * (b + c + 1) / e) * d = a * (b / e * d) + a * (1 / e * d) + a * (c / e * d) :=
by rewrite_search [add_comm, add_assoc, mul_one, mul_assoc, /-mul_comm,-/ left_distrib, right_distrib] {trace_result := tt, trace_summary := tt, /-view := visualiser,-/ metric := edit_distance {refresh_freq := 3} weight.cm, strategy := pexplore, max_iterations := 500}

lemma test5_ring : (a * (b + c + 1) / e) * d = a * (b / e * d) + a * (1 / e * d) + a * (c / e * d) :=
by ring

end tidy.rewrite_search.vs_ring
