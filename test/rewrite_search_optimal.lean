import tidy.rewrite_search
open tidy.rewrite_search.tracer

private axiom foo : [0] = [1]
private axiom bar1 : [1] = [2]
private axiom bar2 : [2] = [3]
private axiom bar3 : [3] = [4]
private axiom bar4 : [4] = [5]
private axiom bar5 : [5] = [6]
private axiom bar6 : [6] = [7]
private axiom baz : [4] = [0]

-- Obviously sub-optimal:
private example : [0] = [7] :=
begin
  rewrite_search_with [foo, bar1, bar2, bar3, bar4, bar5, bar6, baz]
    { optimal := ff, view := no visualiser, trace_result := tt },
end

-- Obviously optimal:
private example : [0] = [7] :=
begin
  rewrite_search_with [foo, bar1, bar2, bar3, bar4, bar5, bar6, baz]
    { optimal := tt, view := visualiser, trace_result := tt },
end