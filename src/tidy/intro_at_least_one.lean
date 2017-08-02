-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

meta def intro_at_least_one : tactic unit :=
do l ← intros,
   guard (¬ l.empty)
