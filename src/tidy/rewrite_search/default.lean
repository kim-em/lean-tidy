-- "init.lean" provides setup wrappers for the rewrite_search core,
-- and the fallback strategy/metric/tracer for the engine.
import .init

-- "tactic.lean" provides the tactics
import .tactic

-- We include the shipped library of strategies, metrics, and tracers.
import .strategy
import .metric
import .tracer

import .bundles

import tidy.command.suggestion