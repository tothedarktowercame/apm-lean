# Product-simplex shuffle parity

`ConstructionTargets.ProductSimplexShuffleParity` adds the integer orientation
sign to the maximal lattice paths exposed by
`ConstructionTargets.ProductSimplexMaximalPaths`.

`IsHorizontal z i` compares the first coordinate at consecutive vertices
`i.castSucc` and `i.succ`. `inversionPairs z` filters all ordered step pairs
`(i,j)` to those with `i < j`, a vertical step at `i`, and a horizontal step at
`j`. `shuffleSign z` is `(-1 : ℤ)` raised to the cardinality of this finite
set. The three exported theorems show that the sign squares to one, is nonzero,
and maps to one in `ZMod 2`.

This module does not pair faces, construct affine realizations, define singular
chains or a chain cross product, or assert Eilenberg-Zilber, Kunneth,
intersection, or consumer results. The next step is to pair maximal paths that
share an interior face, prove their signs are opposite, and identify the
surviving exterior-face signs before affine realization.
