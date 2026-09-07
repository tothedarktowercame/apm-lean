# Disjoint half-radius balls from separated centers

`pairwiseDisjoint_ball_half_of_separated` converts the separation condition on
a finite family of centers into the pairwise-disjoint open balls consumed by
the packing measure estimate.  Distinct centers separated by at least `r` have
disjoint open balls of radius `r / 2`.

This theorem does not construct a maximal separated family, prove that its
balls lie in a bounded enlargement, or derive a cover from maximality.  It also
does not combine the packing bound with Taylor-controlled target-ball volumes.
The remaining Sard obligation is one maximal separated-family construction,
bounded-enlargement containment, and Taylor/volume exponent estimate, before
local rank reduction.
