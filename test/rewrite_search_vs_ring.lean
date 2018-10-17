import tactic.ring
import tidy.rewrite_search

open tidy.rewrite_search.metric
open tidy.rewrite_search.strategy
open tidy.rewrite_search.tracer

namespace tidy.rewrite_search.vs_ring

suggestion arithmetic

constants a b c d e : ℚ

lemma test3 : (a * (b + c)) * d = a * (b * d) + a * (c * d) :=
by rewrite_search {trace_result := tt, trace_summary := tt, view := no visualiser, metric := edit_distance}

lemma test4_ring : (a * (b + c + 1)) * d = a * (b * d) + a * (1 * d) + a * (c * d) :=
by ring

lemma test4 : (a * (b + c + 1)) * d = a * (b * d) + a * (1 * d) + a * (c * d) :=
by rewrite_search {trace_result := tt, trace_summary := tt, view := no visualiser, metric := edit_distance {refresh_freq := 3} weight.cm, strategy := pexplore, max_iterations := 100}

lemma test5_ring : (a * (b + c + 1) / e) * d = a * (b / e * d) + a * (1 / e * d) + a * (c / e * d) :=
by ring

lemma test5 : (a * (b + c + 1) / e) * d = a * (b / e * d) + a * (1 / e * d) + a * (c / e * d) :=
by rewrite_search {trace_result := tt, trace_summary := tt, view := no visualiser}

-- lemma test5_2 : (a * (b + c + 1) / e) * d = a * (b / e * d) + a * (1 / e * d) + a * (c / e * d) :=
-- by rewrite_search [add_comm, add_assoc, mul_one, mul_assoc, /-mul_comm,-/ left_distrib, right_distrib] {trace_result := tt, trace_summary := tt, view := no visualiser, metric := edit_distance {refresh_freq := 10} weight.cm, strategy := pexplore {pop_size := 5}, max_iterations := 500}

-- lemma test5_bfs : (a * (b + c + 1) / e) * d = a * (b / e * d) + a * (1 / e * d) + a * (c / e * d) :=
-- by rewrite_search [add_comm, add_assoc, mul_one, mul_assoc, /-mul_comm,-/ left_distrib, right_distrib] {trace_result := tt, trace_summary := tt, view := no visualiser, metric := edit_distance {refresh_freq := 3} weight.svm, strategy := bfs, max_iterations := 2000}

end tidy.rewrite_search.vs_ring
