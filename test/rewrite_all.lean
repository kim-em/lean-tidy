import tidy.rewrite_all

axiom foo : [1] = [2]

example : [[1], [1], [1]] = [[1], [2], [1]] :=
begin
  perform_nth_rewrite_lhs [foo] 1,
end