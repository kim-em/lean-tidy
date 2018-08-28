-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tactic.tidy

open tactic
set_option trace.tidy true

@[reducible] def {u} auto_cast {α β : Sort u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Sort u} (p : α = α) (a : α) : @auto_cast α α p a = a := 
begin unfold auto_cast, unfold cast, end
notation `⟬` p `⟭` := @auto_cast _ _ (by tidy) p
