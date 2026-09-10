# Balanced-word and maximal-path equivalence

`ConstructionTargets.ProductSimplexWordPathEquivalence` packages the exact
equivalence between `BalancedWord p q` and canonical `MaximalPath p q` values.
Its forward map is `reconstructedPath`, and its inverse is `balancedStepWord`.

The reverse reconstruction law exposes the reconstructed simplex, applies
injectivity of `prodStdSimplex.objEquiv`, and proves equality of both cumulative
coordinates using `horizontalCount_stepWord` and `verticalCount_stepWord`. The
other inverse direction uses the banked `stepWord_reconstructedPath` theorem.

`wordPathEquiv` records these two laws as an equivalence. The module also type
checks all fifteen pairs `(p,q)` with `p+q ≤ 4`.

The module does not define corner swaps, cancel faces, prove shuffle signs,
construct chain sums or a singular cross product, or assert Eilenberg-Zilber,
Kunneth, intersection, or consumer results.
