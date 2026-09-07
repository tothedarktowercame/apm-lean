# Exact-rank local upper locus

This module promotes the compiled derivative-rank semicontinuity interface.

`derivativeRankAtLeast f r` records the points where the cardinal rank of the Fréchet derivative is at least `r`. Continuity of the derivative for a `C¹` map and openness of the finite-dimensional rank lower bound make this locus open.

At a point of exact rank `r`, intersecting with that open lower-rank locus identifies the exact-rank stratum with the locus whose derivative range has finrank at most `r`.

The next consumer step is to select a complemented rank-`r` minor, instantiate the local rank normal form, and prove derivative flatness of the remaining coordinate map along the local rank-at-most-`r` fibre before applying Taylor-cover nullity.
