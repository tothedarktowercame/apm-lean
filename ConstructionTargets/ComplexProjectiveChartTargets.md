# ComplexProjectiveChartTargets

The underlying space and topology are `ProjectiveSpaceTopology.Space ℂ n`. Affine coordinates are the actual ratios rep(x)_j / rep(x)_i for j ≠ i. The inverse inserts 1 in coordinate i and applies the nonzero-vector quotient map.

`AffineChartConstruction` requires open partial homeomorphisms with exactly these maps, the nonzero-coordinate patches, full affine targets, and the prescribed coordinate-line centers. The t99J05 conclusion requests this construction; no inhabitant is assumed. The required patches cover projective space because representatives are nonzero.

Construction targets: ratio independence under rescaling, continuity, inverse laws, patch coverage and smooth chart transitions. Fixed-point index is the sign of the real determinant of id-D(localMap), used only with differentiability and nondegeneracy in the consumer conclusion. Prove the equivalence with the topological local index and the global Lefschetz trace formula. A complex determinant is not substituted for its real counterpart.

The module builds as a named Lake target and is imported by ConstructionTargets.lean. Its definitions contain no `sorry`; consumer theorems remain explicitly unproved. Independent mathematical review is pending.
