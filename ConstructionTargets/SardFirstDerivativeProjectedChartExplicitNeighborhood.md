# First-derivative projected chart explicit neighborhood

`exists_projected_localRankNormalForm_with_explicit_inverse_neighborhood`
turns the eventual inverse-coordinate identities of the projected local-rank
chart into a single explicit neighborhood of the projected base coordinate.
It retains the same derivative-range and projected-kernel coordinate types,
base-point chart-source membership, and exact forward chart formula.

Throughout the returned neighborhood, projection of `f (e.symm p)` to the
base derivative range is `p.1`, while projection of `e.symm p` to the
projected derivative kernel is `p.2`.  Thus fixed first-coordinate slices can
be restricted to an actual neighborhood before differentiation.

The next step is to combine these pointwise identities with the compiled
constant-coordinate slice and local residual derivative-flatness theorems,
then derive pointwise local image nullity for each order-one exact-rank piece.
