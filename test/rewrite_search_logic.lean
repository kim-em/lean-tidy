import logic.basic
import tidy.tidy
open tidy.rewrite_search.tracer
open tidy.rewrite_search.metric

local attribute [instance] classical.prop_decidable

example {A B C : Prop} : _ = _ :=
calc
        ((B → C) → (¬(A → C)     ∧ ¬(A ∨ B)))
      = ((B → C) → (¬(¬A ∨ C)    ∧ ¬(A ∨ B)))         : by rw ← imp_iff_not_or
  ... = ((B → C) → ((¬(¬A) ∧ ¬C) ∧ ¬(A ∨ B)))         : by rw not_or_distrib
  ... = ((B → C) → ((¬(¬A) ∧ ¬C) ∧ (¬A ∧ ¬B)))        : by rw not_or_distrib
  ... = ((B → C) → ((A ∧ ¬C) ∧ (¬A ∧ ¬B)))            : by rw not_not
  ... = ((B → C) → ((A ∧ ¬C) ∧ ¬A ∧ ¬B))              : by rw and_assoc
  ... = ((B → C) → ((¬C ∧ A) ∧ ¬A ∧ ¬B))              : by rw and_comm (A) (¬C)
  ... = ((B → C) → (¬C ∧ A ∧ ¬A ∧ ¬B))                : by rw and_assoc
  ... = ((B → C) → (¬C ∧ (A ∧ ¬A) ∧ ¬B))              : by rw and_assoc
  ... = ((B → C) → (¬C ∧ ¬ B ∧ (A ∧ ¬A)))             : by rw and_comm (¬ B) (A ∧ ¬A)
  ... = ((B → C) → (¬C ∧ ¬ B ∧ false ))               : by rw and_not_self_iff A
  ... = ((B → C) → ((¬C) ∧ false ))                   : by rw and_false
  ... = ((B → C) → (false))                           : by rw and_false
  ... = (¬(B → C) ∨ false)                            : by rw imp_iff_not_or
  ... = ¬(B → C)                                      : by rw or_false
  ... = ¬(¬B ∨ C)                                     : by rw imp_iff_not_or
  ... = ((¬¬B) ∧ (¬C))                                : by rw not_or_distrib
  ... = (B ∧ ¬C)                                      : by rw not_not

local attribute [search] imp_iff_not_or not_or_distrib not_not and_assoc and_comm and_not_self_iff and_false not_not

example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
  by rewrite_search_using [`search]

-- Vanilla
example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
by
  rewrite_search_using [`search] {view := no visualiser, trace_summary := tt}

-- CM
example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
by
  rewrite_search_using [`search] {view := no visualiser, trace_summary := tt, metric := edit_distance {refresh_freq := 10} weight.cm}

-- libSVM refresh every 20
example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
by
  rewrite_search_using [`search] {view := no visualiser, trace_summary := tt, metric := edit_distance {refresh_freq := 20} weight.svm}

-- libSVM refresh every 15
example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
by
  rewrite_search_using [`search] {view := no visualiser, trace_summary := tt, metric := edit_distance {refresh_freq := 15} weight.svm}

-- libSVM refresh every 10
example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
by
  rewrite_search_using [`search] {view := no visualiser, trace_summary := tt, metric := edit_distance {refresh_freq := 10} weight.svm}

-- libSVM refresh every 5
example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
by
  rewrite_search_using [`search] {view := no visualiser, trace_summary := tt, metric := edit_distance {refresh_freq := 5} weight.svm}

-- libSVM refresh every 1
example {A B C : Prop} : ((B → C) → (¬(A → C) ∧ ¬(A ∨ B))) = (B ∧ ¬C) :=
by
  rewrite_search_using [`search] {view := no visualiser, trace_summary := tt, metric := edit_distance {refresh_freq := 1} weight.svm}