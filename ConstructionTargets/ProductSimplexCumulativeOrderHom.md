# Product simplex cumulative order homomorphism

This module turns the prefix counts of a `BalancedWord p q` into bounded grid
coordinates.  At each prefix endpoint, `gridVertex` uses the horizontal count
as an element of `Fin (p + 1)` and the vertical count as an element of
`Fin (q + 1)`; the bounds come directly from the balanced-word terminal-total
theorems.

`cumulativeOrderHom` packages these vertices as an order homomorphism.  Its
monotonicity proof uses the exported horizontal and vertical prefix-count
monotonicity theorems coordinatewise.  The two projection lemmas expose the
coordinates definitionally, and `cumulativeOrderHom_coordinate_sum` states
that their natural-number sum is exactly the prefix endpoint.

The module stops before applying `prodStdSimplex.objEquiv.invFun`.  It does not
construct a simplex or maximal path, prove nondegeneracy or inverse laws,
define corner swaps, cancel faces, or construct singular chains or a cross
product.
