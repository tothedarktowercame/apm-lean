# Euclidean sphere pole-overlap adapter

This target specializes `PuncturedNormedSpaceRadialEquivalence` to the metric
spheres used by the topology problems:

```lean
Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
```

The canonical pole is the first standard basis vector.  Mathlib's
`OrthonormalBasis.fromOrthogonalSpanSingleton` supplies a linear isometry from
its orthogonal complement to `EuclideanSpace ℝ (Fin n)`.  Restricting that
isometry to unit spheres and composing with the abstract two-pole radial
equivalence proves that the two-pole complement is homotopy equivalent to the
lower-dimensional sphere.  The target also records the corresponding product
homotopy equivalence.

The construction includes `n = 0`: the orthogonal complement and `Fin 0`
space are both zero-dimensional, while their unit spheres are empty.  No
nonemptiness claim is made.

This is geometric infrastructure only.  It contains no homology,
Mayer–Vietoris, or problem-level vanishing statement.
