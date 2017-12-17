[![Build Status](https://travis-ci.org/semorrison/lean-tidy.svg?branch=master)](https://travis-ci.org/semorrison/lean-tidy)

A library of tactics for lean. These are used in the category theory library.

Highlights include `chain` and `tidy`.

Here's the basic idea. The `tidy` tactic attempts to do as much as possible of the "obvious" steps in a proof. In particular, it has a long (ordered) list of tactics, and at each step it finds the first tactic that succeeds, and if there is one that succeeds, it tries again. The current list of tactics is given by these two functions:

````
meta def unsafe_tidy_tactics : list (tactic string) :=
[
  assumption >> pure "assumption",
  congr_assumptions,
  `[simp only [id_locked_eq]]                 >> pure "simp only [id_locked_eq]"
]

meta def safe_tidy_tactics : list (tactic string) :=
[
  force (reflexivity)                         >> pure "refl", 
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  applicable                                  >>= λ n, pure ("fapply " ++ n.to_string),
  intro_at_least_one                          >> pure "intros",
  force (fsplit)                              >> pure "fsplit", 
  dsimp'                                      >> pure "dsimp'",
  `[simp]                                     >> pure "simp",
  automatic_induction                         >> pure "automatic_induction",
  dsimp_all'                                  >> pure "dsimp_all'",
  `[simp at *]                                >> pure "simp at *"
]
````

A few notes:
* For now ignore the difference between the two lists; this is explained below.
* Each of these is setup as a "tactic string", which returns the command a user would enter in tactic mode. Using the command `tidy { trace_result := tt }` outputs the entire sequence of commands used, making it easy to replace a call to tidy with a sequence of explicit calls to the underlying tactics.
* One can also pass extra tactics using `tidy { extra_tactics := [ ... ] }`, although these tactics are only tried after all the built-in ones. (I'd like to make this more flexible.)
* There's also a `@tidy` attribute. Putting this on a definition that returns a `tactic unit` or `tactic string` will include that tactic in the list.
* Because tidy relies on checking whether a tactic succeeds or fails, we need to wrap some of the basic commands (like `reflexivity` and `fsplit`) with `force`, to verify that they actually did something, and didn't just "fail silently".
* `applicable` is the most interesting tactic here. There is an attribute `@applicable` which one can add to lemmas, and the `applicable` tactic will automatically `apply` any such lemma to the current goal. The idea here is that if you have a lemma which is the only possible way to prove a certain goal, it is always safe to apply it. 
* Other non-standard tactics are `automatic_induction` which applies induction to variety of simple types (pairs, units, etc), and `dsimp'` which is just an abbreviation for `dsimp {unfold_reducible := tt, md := semireducible}`.
* The difference between a nonsafe and safe tactic is that nonsafe tactics are only applied if there is only one goal, or if the first goal is a mere proposition. The main nonsafe tactic we use is `assumption`. (The point being that if there are further goals, perhaps depending on the first one, it can be incorrect to solve the first goal with just any hypothesis of the correct type.)
* Because in the category theory library I've marked many of the lemmas of the form "to prove two natural transfomations are equal, you can check that they are componentwise equal" as @applicable, the tidy tactic tends to prove things by writing everything out in components! This is a feature of our choices of where to use @applicable, and not intrinsic to `tidy`.

I'm very happy to have examples of goals that `tidy` does something stupid with. I'm very happy to have suggestions of improvements to the list of tactics `tidy` uses, that would make it more useful in other problem domains. I'm thinking about ways to produce better output as well --- at the moment we can use `tidy { trace_result := tt }` to get the list of commands used, but I'd love to have, for example `tidy { latex_output := tt }` produce something human readable!

