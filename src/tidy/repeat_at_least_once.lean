-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

namespace tactic

meta def repeat_at_least_once ( t : tactic unit ) : tactic unit := t >> repeat t

run_cmd add_interactive [`repeat_at_least_once]

end tactic