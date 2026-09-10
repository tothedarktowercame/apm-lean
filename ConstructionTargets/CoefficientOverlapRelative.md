# Relative overlap inclusion square

`ConstructionTargets.CoefficientOverlapRelative` lifts the reviewed translated chart-overlap geometry to actual deleted-point subtype-cokernel chain maps over an arbitrary Type 0 commutative ring R. M is Type 0 and charted on EuclideanSpace ℝ (Fin (m+2)); x belongs to the common chart source. No separation hypothesis is needed for these comparisons. Ambient neighborhood excision retains its separate Hausdorff hypotheses.

The four MapsTo proofs show that the transition and its inverse preserve deletion of zero, and the two ambient coordinate maps carry deletion of zero into M minus x. `transitionMap`, `inverseMap`, `leftMap` and `rightMap` are the actual reviewed pairMap constructions on these literal subsets.

`relative_square` states transitionMap followed by rightMap equals leftMap. Its proof uses actual pair-map composition and the geometric ambient square. `homology_square` applies the actual homology functor in every natural degree, including zero. The four projection theorems give the exact degreewise cokernel-projection equations for all four maps.

`inverse_left` and `inverse_right` derive the transition inverse laws from geometric inverse equations and actual pair identity/composition. `relativeIso` uses these exact maps on the deleted-zero complexes; `homologyIso` applies the homology functor. Integer and rational square examples and sixteen standard-only axiom audits are included.

The Lean source exactly matches fixture SHA256 b573fd1815d0cef5c0c4e098bc4da3860cd830d70640f5c925a83587f610e406. This packet proves the relative square and transition invertibility. Ambient-map invertibility and comparison of chart-based normalizations remain downstream through neighborhood excision. Recovering the distinguished-chart normalization, transition units, generator-change and directed cocycle equations remains separate, as do orientation coherence and consumer closure.
