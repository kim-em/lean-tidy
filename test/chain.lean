import tidy.monadic_chain

open tactic

namespace tidy.test

def chain_test_simp_succeeded : 1 = 1 :=
begin
  chain [ interactive_simp ]
end

def chain_test_without_loop_detection_skip_does_nothing : 1 = 1 :=
begin
  success_if_fail { chain [ skip ] { fail_on_loop := ff, fail_on_max_steps := tt } }, -- fails because 'chain iteration limit exceeded'
  refl
end

def chain_test_without_loop_detection_skip_does_nothing' : 1 = 1 :=
begin
  success_if_fail { chain [ skip, interactive_simp ] { fail_on_loop := ff, fail_on_max_steps := tt } }, -- fails because 'chain iteration limit exceeded'
  refl
end

def chain_test_loop_detection : 1 = 1 :=
begin
  chain [ skip, interactive_simp ] {}
end

def chain_test_loop_detection' : 1 = 1 :=
begin
  chain [ skip, interactive_simp ] { allowed_collisions := 5, trace_steps := tt }
end

end tidy.test