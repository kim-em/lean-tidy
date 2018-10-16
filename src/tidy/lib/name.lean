namespace name

def get_suffix : name → option string
| anonymous        := none
| (mk_string s p)  := s
| (mk_numeral n p) := to_string n

def append_suffix : name → string → name
| anonymous suff        := mk_string suff anonymous
| (mk_string s p) suff  := mk_string (s ++ suff) p
| (mk_numeral n p) suff := mk_string (to_string n ++ suff) p

meta def chop_reserved_name (new_top_level : name := anonymous) : name → name
| anonymous                := anonymous
| (mk_numeral n anonymous) := mk_string ("n" ++ to_string n)     new_top_level
| (mk_string  s anonymous) := mk_string s.to_list.tail.as_string new_top_level
| (mk_numeral n pfx)       := mk_string ("n" ++ to_string n) $ chop_reserved_name pfx
| (mk_string  s pfx)       := mk_string s                    $ chop_reserved_name pfx

meta def mk_user_fresh_name (pfx : string := "") (sfx : string := "") : tactic name := do
  let pfx_name := if pfx.length = 0 then anonymous else mk_string pfx anonymous,
  chopped ← chop_reserved_name pfx_name <$> tactic.mk_fresh_name,
  return $ if sfx.length = 0 then chopped else mk_string sfx chopped

end name