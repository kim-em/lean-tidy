-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .if_then_else

open tactic
open nat

-- FIXME how do we set options? It's annoying to have to pass a configuration everywhere.

structure chain_cfg := 
  ( max_steps     : nat  := 500 )
  ( trace_steps   : bool := ff )
  ( fail_on_loop  : bool := tt )
  ( trace_on_loop : bool := tt )

meta def hash_target : tactic string :=
(done >> pure "no goals") <|>
do options ← get_options,
   set_options (options.set_bool `pp.all true),
   t ← read, 
   set_options options,
   pure t.to_format.to_string

private meta structure chain_progress { α : Type } :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (tactic α) )
  ( hashes            : list string )
  ( repeats           : nat )

private meta def chain' { α : Type } [ has_to_format α ] ( cfg : chain_cfg ) ( tactics : list (tactic α) ) : chain_progress → tactic (list α)
| ⟨ 0,      results, _, hashes, _ ⟩ := trace (format!"... chain tactic exceeded iteration limit {cfg.max_steps}") >>
                                     trace results.reverse >> 
                                     failed   
| ⟨ _,      results, [], _, _ ⟩     := (pure results)
| ⟨ succ n, results, t :: ts, hashes, repeats ⟩ :=
    if_then_else done
      (pure results)
      (do if cfg.trace_steps then trace format!"trying chain tactic #{tactics.length - ts.length}" else skip,
          some r ← try_core t | /- tactic t failed, continue down the list -/ (chain' ⟨ succ n, results, ts, hashes, repeats ⟩),
          h ← hash_target,
          let
          if hashes.mem h then 
            /- we've run into a loop -/
            do if cfg.fail_on_loop || cfg.trace_on_loop then trace "chain tactic detected looping" else skip,
               if cfg.fail_on_loop then
                 trace results.reverse >> failed
               else 
                 /- continue down the list -/
                 (chain' ⟨ succ n, results, ts, hashes, repeats ⟩)
          else 
            do (if cfg.trace_steps then trace format!"succeeded with result: {r}" else skip),  
                (chain' ⟨ n, r :: results, tactics, h :: hashes ⟩ )
      )

meta def chain { α : Type } [ has_to_format α ] 
  ( tactics        : list (tactic α) )
  ( cfg     : chain_cfg := {} )
    : tactic (list α) :=
do sequence ← chain' cfg tactics ⟨ cfg.max_steps, [], tactics, [] ⟩,
   guard (sequence.length ≠ 0) <|> fail "...chain tactic made no progress",
   pure sequence.reverse