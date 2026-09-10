# Affine realization of maximal product-simplex paths

`ConstructionTargets.ProductSimplexAffineRealization` gives the exact
face-compatible representation map from canonical maximal simplicial-product
paths to continuous affine simplices in a product of topological standard
simplices.

For a maximal path `z`, `gridVertex z i` turns the two coordinates of
`prodStdSimplex.objEquiv z.1 i` into the corresponding standard-simplex basis
vertices. `productAffine` affinely realizes an arbitrary ordered family of such
product vertices, coordinate by coordinate, and `pathRealization` specializes
it to the vertices of `z`.

`productAffine_standardVertex` and `pathRealization_standardVertex` prove exact
values on basis vertices. `affineSimplex_standardVertex'` supplies the generic
basis evaluation used by the construction. `productAffine_comp_face` proves
that precomposing with `faceAffine n i` is exactly the affine realization of
the ordered vertex family with vertex `i` deleted through `i.succAbove`.
Because the construction is uniform in `p` and `q`, every downstream case with
`p + q ≤ 4` is an immediate instance.

The module does not prove oriented face cancellation, define chain sums or a
singular cross product, or assert Eilenberg-Zilber, Kunneth, intersection, or
consumer results. The next step combines this face formula with shuffle parity
to cancel interior faces and identify the surviving Leibniz boundary terms.
