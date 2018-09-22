meta def options.set_list : options → list (name × bool) → options
| o []               := o
| o ((n, v) :: rest) := (o.set_bool n v).set_list rest