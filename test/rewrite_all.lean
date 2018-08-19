import tidy.rewrite_all

axiom foo : [1] = [2]

example : [[1], [1], [1]] = [[1], [2], [1]] :=
begin
  nth_rewrite_lhs 1 [foo],
end