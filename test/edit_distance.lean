import tidy.edit_distance

open edit_distance_progress

#eval edit_distance' [1,2,3,4] [1,2,3,4]

def f0 : partial_edit_distance_data ℕ := ⟨ 0, [7,8,9], [1,2,3,4,5] ⟩ 
def p0 : edit_distance_progress [7,8,9] [7,8,19,8,9] := at_least [7,8,9] [7,8,19,8,9]  0 f0

meta def p1 := update_edit_distance p0
meta def p2 := update_edit_distance p1
meta def p3 := update_edit_distance p2
meta def p4 := update_edit_distance p3
meta def p5 := update_edit_distance p4

#eval p0.to_string
#eval p1.to_string
#eval p2.to_string
#eval p3.to_string
#eval p4.to_string
