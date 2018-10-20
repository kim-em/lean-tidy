-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison

import .tactic
import .discovery

open tactic

variables {α β γ δ : Type}

namespace tactic.interactive

open lean.parser interactive
open tidy.rewrite_search

meta def rewrite_search (try_harder : parse $ optional (tk "!")) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string :=
  tidy.rewrite_search.rewrite_search (¬try_harder.is_none) cfg

meta def rewrite_search_with (try_harder : parse $ optional (tk "!")) (rs : parse rw_rules) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string :=
  tidy.rewrite_search.rewrite_search_with (¬try_harder.is_none) rs.rules cfg

meta def rewrite_search_using (try_harder : parse $ optional (tk "!")) (as : list name) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string :=
  tidy.rewrite_search.rewrite_search_using (¬try_harder.is_none) as cfg

-- @Scott should we still do this?
--  exprs ← close_under_apps exprs, -- TODO don't do this for everything, it's too expensive: only for specially marked lemmas

-- @Keeley, the ideal thing would be to look for lemmas that have a metavariable for their LHS,
-- and try substituting in hypotheses to these.

meta def simp_search (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic unit :=
  tidy.rewrite_search.simp_search cfg

meta def simp_search_with (rs : parse rw_rules) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic unit :=
  tidy.rewrite_search.simp_search_with rs.rules cfg

end tactic.interactive
