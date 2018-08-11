-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek

import tactic.ring
import tactic.interactive

open lean
open lean.parser

open tactic
open ring
open interactive interactive.types expr

meta def rwing (q : parse interactive.rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
try (interactive.ring1 <|>
do ns ← l.get_locals,
   tt ← tactic.replace_at (ring.normalize ring.normalize_mode.SOP) ns l.include_goal,
   when l.include_goal $ try tactic.reflexivity)
>> interactive.rewrite q l cfg >> try interactive.ring1

namespace tactic.interactive
  meta def rwing (q : parse interactive.rw_rules) (l : parse location) (cfg : rewrite_cfg := {md := semireducible}) : tactic unit := _root_.rwing q l cfg
end tactic.interactive