My short terms goals now:
1) Restore "tactic script" output, so we can actually see which rewrites are happening, and restore the ability to remove obviously, replacing it by its script output. (Realistically, in library use sometimes obviously is too slow, or too gross a dependency.)
2) Work out if and why the new search is finding longer paths than the old search. In particular in currying_2.lean there is an example where apparently we used to find a string of 3 rewrites, but now we find 7.
3) Do a breadth first search strategy, just as warmup to:
4) Implement a mode that runs whatever "real" search strategy we're using, and then after it finds a path continues working. It would be lovely if all the new nodes it finds after finding a first connecting path were rendered in the visualiser in a ghostly grey, so it's completely visually clear which nodes were searched for real, and which ones are just there to show us the geometry of the entire search space, and give an indication of how well the algorithm performed.

I can probably manage all of these myself, although you might be more efficient at 4).

After those, I will probably turn to my two toy demo ideas: knot isotopy via rewriting, and the rubiks cube.

The more interesting goals are:
1) Implement "centre of mass" based weights on edit distance. This could either be done _once_, looking at the initial goal, or after some number of steps, or even every step (perhaps makes edit distance computations too expensive?)
2) classifier based weights
3) start thinking either about "lemma selection" (see attached article?) or even better "generating approximate intermediate goals" after determining based on classification that a certain lemma is "the essential step".
