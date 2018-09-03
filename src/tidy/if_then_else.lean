-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

def if_then_else { α β : Type } { m : Type → Type } [monad m] [has_orelse m] ( i : m α ) ( t e : m β ) : m β :=
do r ← (i >> pure tt) <|> pure ff,
   if r then do t else do e

def dependent_if_then_else { α β : Type } { m : Type → Type } [monad m] [has_orelse m] ( i : m α ) ( t : α → m β ) ( e : m β ) : m β :=
do r ← i >>= (λ x, pure (some x)) <|> pure none,
   match r with
   | some a := t a
   | none   := e
   end
