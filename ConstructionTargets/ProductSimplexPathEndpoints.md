# Endpoints of maximal product-simplex paths

`ConstructionTargets.ProductSimplexPathEndpoints` records the exact endpoint
normalization needed for Boolean-word cardinality and path reconstruction.

`grid_start` proves that every canonical maximal path begins at `(0,0)`. It
evaluates `maximalPath_coordinate_sum` at time zero and derives both coordinate
equalities in natural numbers. `grid_end` proves that the terminal vertex is
`(p,q)`. It combines the coordinate sum at `Fin.last (p+q)` with the `isLt`
bounds on both finite coordinates, then returns an exact equality in the
canonical `prodStdSimplex.objEquiv` representation.

The module proves no word cardinality, path reconstruction, corner swap, face
pairing, sign change, cancellation, chain sum, cross product,
Eilenberg-Zilber, Kunneth, intersection, or consumer result. The next step uses
these endpoints and local step semantics to count `p` horizontal and `q`
vertical letters, reconstruct cumulative-coordinate paths, and implement the
adjacent unlike-letter swap.
