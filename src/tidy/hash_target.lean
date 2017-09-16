-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

meta def hash_target : tactic string :=
(done >> pure "[no goals]") <|>
do options ← get_options,
   set_options (options.set_bool `pp.all true),
   t ← read,
   set_options options,
   pure t.to_format.to_string