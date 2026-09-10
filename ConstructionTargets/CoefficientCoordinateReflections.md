# Coordinate-reflection conjugation

`ConstructionTargets.CoefficientCoordinateReflections` constructs real coordinate reflections and permutations as linear isometry equivalences, restricts them to actual unit-sphere homeomorphisms, and proves conjugation on actual singular homology with coefficients `ModuleCat.of R R` for any Type 0 commutative ring R.

The permutation convention is `permutation e x j = x (e.symm j)`: x is composed with the inverse permutation. Reflection i negates coordinate i and fixes the other coordinates. Pointwise conjugation P(e) ∘ reflection(i) ∘ P(e inverse) equals reflection(e i). The inverse-permutation identity is proved directly on coordinates.

`homology_conjugation` applies the actual singular homology functor in every natural degree q. In categorical composition order, the inverse permutation map comes first, then reflection i, then the permutation map; their composite equals the map of reflection (e i). `homology_permutation_inverse` proves the corresponding inverse equation.

`transport_negative` explicitly assumes that reflection i acts by minus identity in degree q and concludes the same for reflection (e i). It assumes no scalar action for the conjugating permutation. `transport_any_coordinate` uses the transposition of i and j to transport that supplied sign to any coordinate j. These are conditional sign-transport theorems, not a proof of the first-coordinate sign.

Geometry is `EuclideanSpace ℝ (Fin d)` and remains separate from the coefficient ring. Coordinate-indexed statements take actual `Fin d` indices. No nonemptiness, field, nontriviality or characteristic hypothesis is added. Integer circle-degree and rational two-sphere-degree conjugation examples are included.

The source is promoted byte-for-byte from `/tmp/CoefficientCoordinateReflections.lean`, SHA256 `e85522027b7e02a970f1c7329d447861d6b770a63a516367fca1562938941aa4`, including ten axiom audits.

Positive-dimensional top-homology coordinates, the first-coordinate reflection sign from the circle base and sphere-shift induction, and the product-to-negation equation remain before antipodal scalar action. This packet claims no antipodal action theorem or consumer closure.
