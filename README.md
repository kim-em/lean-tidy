This library is essentially deprecated: all the useful stuff is either already in `mathlib`, or in the [lean-rewrite-search](https://github.com/semorrison/lean-rewrite-search) repository.



[![Build Status](https://travis-ci.org/semorrison/lean-tidy.svg?branch=master)](https://travis-ci.org/semorrison/lean-tidy)

A library of tactics for lean. These are used in the category theory library.

Highlights include `chain` and `tidy`.

Here's the basic idea. The `tidy` tactic attempts to do as much as possible of the "obvious" steps in a proof. In particular, it has a long (ordered) list of tactics, and at each step it finds the first tactic that succeeds, and if there is one that succeeds, it tries again. The current list of tactics is:

````
[ force (reflexivity)                         >> pure "refl",
  exact_decidable,
  propositional_goal >> assumption            >> pure "assumption",
  forwards_reasoning,
  forwards_library_reasoning,
  backwards_reasoning,
  `[ext1]                                     >> pure "ext1",
  intro_at_least_one                          >>= λ ns, pure ("intros " ++ (" ".intercalate ns)),
  automatic_induction,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  fsplit                                      >> pure "fsplit",
  injections_and_clear                        >> pure "injections_and_clear",
  terminal_goal >> (`[solve_by_elim])         >> pure "solve_by_elim",
  unfold_aux                                  >> pure "unfold_aux",
  run_tidy_tactics ]
  ````

A few notes:
* Each of these is setup as a "tactic string", which returns the command a user would enter in tactic mode. Using the command `tidy { explain := tt }` outputs the entire sequence of commands used, making it easy to replace a call to tidy with a sequence of explicit calls to the underlying tactics.
* One can also pass extra tactics using `tidy { extra_tactics := [ ... ] }`, although these tactics are only tried after all the built-in ones. (I'd like to make this more flexible.)
* There's also a `@tidy` attribute. Putting this on a definition that returns a `tactic unit` or `tactic string` will include that tactic in the list.
* Because tidy relies on checking whether a tactic succeeds or fails, we need to wrap some of the basic commands (like `reflexivity` and `fsplit`) with `force`, to verify that they actually did something, and didn't just "fail silently".
* To make use of `backwards_reasoning` you need to tag lemmas with `@[back]`; these are then applied to the goal wherever possible. (The attribute `@[back']` allows the more conservative approach that the lemma should be applied to the goal so long as all new goals can be solved directly from hypotheses.)
* To make use of `forwards_library_reasoning` you need to tag lemmas with `@[forward]`.
* The other non-standard tactic is `automatic_induction` which applies induction to variety of simple types (pairs, units, etc).
* Because `ext1` is on the list, the tidy tactic tends to prove things by writing everything out in components!

I'm very happy to have examples of goals that `tidy` does something stupid with. I'm very happy to have suggestions of improvements to the list of tactics `tidy` uses, that would make it more useful in other problem domains. I'm thinking about ways to produce better output as well --- at the moment we can use `tidy { explain := tt }` to get the list of commands used, but I'd love to have, for example `tidy { latex_output := tt }` produce something human readable!

Not described here (yet) are `rewrite_search` and `obviously` (which is just `tidy` followed by `rewrite_search`.)

