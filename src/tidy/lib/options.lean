meta def options.set_list_bool : options → list (name × bool) → options
| o []               := o
| o ((n, v) :: rest) := (o.set_bool n v).set_list_bool rest