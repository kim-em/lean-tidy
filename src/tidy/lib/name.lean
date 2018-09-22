namespace name

def get_suffix : name → option string
| anonymous        := none
| (mk_string s p)  := s
| (mk_numeral n p) := to_string n

def append_suffix : name → string → name
| anonymous suff        := mk_string suff anonymous
| (mk_string s p) suff  := mk_string (s ++ suff) p
| (mk_numeral n p) suff := mk_string (to_string n ++ suff) p

end name