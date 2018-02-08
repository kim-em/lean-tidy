
import system.io

open tactic

universe variables u

/-- This function has a native implementation that returns the system time in microseconds since the epoch. -/
-- see patch below for adding this to Lean
-- it currently suffers from overflow issues, which aren't a problem for profiling.
meta def systemtime : ℕ :=
0

-- There's apparently about a 1/5th of a second overhead here...
-- meta def time_in_millis : tactic ℕ :=
-- do time ← tactic.unsafe_run_io (io.cmd { cmd := "gdate", args := [ "+%s%N" ] }),
--    pure (time.to_nat / 1000000)

meta def time_in_micros : tactic ℕ := pure systemtime

-- measure in millis
meta def time_tactic { α : Type } ( t : tactic α ) : tactic (α × ℕ) :=
do time_before ← time_in_micros,
   r ← t,
   time_after ← time_in_micros,
   pure (r, (time_after - time_before))


-- the following patch adds a builtin `systemtime`

-- diff --git a/src/library/vm/vm_aux.cpp b/src/library/vm/vm_aux.cpp
-- index 738f5bab2..4bc6bdc8a 100644
-- --- a/src/library/vm/vm_aux.cpp
-- +++ b/src/library/vm/vm_aux.cpp
-- @@ -20,6 +20,10 @@ vm_obj vm_timeit(vm_obj const &, vm_obj const & s, vm_obj const & fn) {
--      return invoke(fn, mk_vm_unit());
--  }
 
-- +vm_obj vm_systemtime() {
-- +    return mk_vm_nat(std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::system_clock::now().time_since_epoch()).count());
-- +}
-- +
--  vm_obj vm_trace(vm_obj const &, vm_obj const & s, vm_obj const & fn) {
--      tout() << to_string(s) << "\n";
--      return invoke(fn, mk_vm_unit());
-- @@ -58,6 +62,7 @@ vm_obj vm_try_for(vm_obj const &, vm_obj const & n, vm_obj const & thunk) {
 
--  void initialize_vm_aux() {
--      DECLARE_VM_BUILTIN("timeit",           vm_timeit);
-- +    DECLARE_VM_BUILTIN("systemtime",       vm_systemtime);
--      DECLARE_VM_BUILTIN("trace",            vm_trace);
--      DECLARE_VM_BUILTIN("trace_call_stack", vm_trace_call_stack);
--      DECLARE_VM_BUILTIN("sorry",            vm_sorry);

