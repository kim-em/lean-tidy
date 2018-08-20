-- Never import tidy.rewrite_search.init directly. Go through me.
-- "init.lean" provides the fallback strategy and tracer for the engine.
import .init

-- 'tactic.lean' provides the tactics
import .tactic

import .tracer
import .strategy