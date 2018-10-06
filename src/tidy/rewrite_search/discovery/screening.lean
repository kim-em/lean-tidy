import tidy.lib.list
import tidy.lib.env
import tidy.lib.tactic
import tidy.lib.pretty_print

open tactic tactic.interactive
open interactive

namespace tidy.rewrite_search.discovery

-- TODO make sure this didn't break anything
meta def is_acceptable_rewrite (t : expr) : bool :=
  is_eq_or_iff_after_binders t

meta def is_acceptable_lemma (r : expr) : tactic bool :=
  is_acceptable_rewrite <$> infer_type r

meta def is_acceptable_hyp (r : expr) : tactic bool :=
  do t ← infer_type r, return $ is_acceptable_rewrite t ∧ ¬t.has_meta_var

meta def assert_acceptable_lemma (r : expr) : tactic unit := do
  ret ← is_acceptable_lemma r,
  if ret then return ()
  else do
    pp ← pretty_print r,
    fail format!"\"{pp}\" is not a valid rewrite lemma!"

meta def load_attr_list : list name → tactic (list name)
| [] := return []
| (a :: rest) := do
  names ← attribute.get_instances a,
  l ← load_attr_list rest,
  return $ names ++ l

meta def load_names (l : list name) : tactic (list expr) :=
  l.mmap mk_const

meta def rewrite_list_from_rw_rules (rws : list rw_rule) : tactic (list (expr × bool)) :=
  rws.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm))

meta def rewrite_list_from_lemmas (l : list expr) : list (expr × bool) :=
  l.map (λ e, (e, ff)) ++ l.map (λ e, (e, tt))

meta def rewrite_list_from_lemma (e : expr) : list (expr × bool) :=
  rewrite_list_from_lemmas [e]

meta def rewrite_list_from_hyps : tactic (list (expr × bool)) := do
  hyps ← local_context,
  rewrite_list_from_lemmas <$> hyps.mfilter is_acceptable_hyp

-- TODO mk_apps recursively
meta def inflate_under_apps (locals : list expr) : expr → tactic (list expr)
| e := do
  rws ← list.map prod.fst <$> mk_apps e locals,
  rws_extras ← list.join <$> rws.mmap inflate_under_apps,
  return $ e :: (rws ++ rws_extras)

meta def inflate_rw (locals : list expr) : expr × bool → tactic (list (expr × bool))
| (e, sy) := do
  as ← inflate_under_apps locals e,
  return $ as.map $ λ a, (a, sy)

meta def is_rewrite_lemma (d : declaration) : option (name × expr) :=
  let t := d.type in if is_acceptable_rewrite t then some (d.to_name, t) else none

meta def find_all_rewrites : tactic (list (name × expr)) := do
  e ← get_env,
  return $ e.decl_omap is_rewrite_lemma

end tidy.rewrite_search.discovery