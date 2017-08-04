-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Mario Carneiro

open tactic

meta def recover : tactic unit :=
do r ← result,
   set_goals $ r.fold [] $ λ e _ l,
     match e with
     | expr.mvar _ _ _ := insert e l
     | _ := l
     end