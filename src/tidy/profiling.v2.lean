-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

class annotation ( β : Type ) := 
  ( pure_update : Π { α : Type }, α → β → β )

meta structure annotated_tactic_state ( β : Type ) [annotation β] :=
  ( annotation   : β )
  ( tactic_state : option tactic_state )

meta def tactic_pure { α : Type } ( a : α ) : tactic α := pure a

meta def annotated_tactic_state.pure { α : Type } ( a : α ) { β : Type } [annotation β] ( s : annotated_tactic_state β ) ( ts : tactic_state ): annotated_tactic_state β :=
{
  annotation   := annotation.pure_update a s.annotation,
  tactic_state := match (tactic_pure a ts) with
                  | result.success _ ts' := some ts'
                  | _ := none
                  end
}

meta instance annotated_tactic_state.monad { β : Type } [annotation β]: monad (interaction_monad (annotated_tactic_state β)) := {
  pure := λ { α : Type } ( a : α ) ( s : annotated_tactic_state β ), 
            match s.tactic_state with 
            | (some ts) := result.success a (annotated_tactic_state.pure a s ts)
            | none      := sorry
            end,
  bind := sorry,
  id_map     := undefined,
  pure_bind  := undefined,
  bind_assoc := undefined,
}

