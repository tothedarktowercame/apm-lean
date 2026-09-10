# Maximal product-simplex lattice paths

`ConstructionTargets.ProductSimplexMaximalPaths` exposes Mathlib's unsigned
combinatorial description of maximal nondegenerate simplices in a product of
standard simplices.

`MaximalPath p q` is the subtype of nondegenerate `(p + q)`-simplices of
`Δ[p] ⊗ Δ[q]`. `mem_maximalPath_iff` restates Mathlib's exact maximal-dimension
criterion: the order homomorphism formed by summing the two path coordinates
is the identity. `maximalPath_coordinate_sum` evaluates that identity at a
vertex, with the coordinate sum on the left and its time index on the right.
`face_objEquiv` records that the `i`th simplicial face deletes vertex `i`, so
its vertex `j` is the original vertex `i.succAbove j`.

This module contains no signs, affine realizations, singular chains, chain
cross product, Eilenberg-Zilber or Kunneth theorem. The next step is to add
integer shuffle parity, pair oriented interior faces, and realize the bounded
paths affinely in total degree at most four.
