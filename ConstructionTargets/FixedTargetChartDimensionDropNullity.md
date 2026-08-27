# Fixed-target-chart dimension-drop nullity

For a `C¹` map between finite-dimensional manifolds whose source model has
strictly smaller real finrank, this target proves nullity of the range in any
chosen target extended chart, relative to an explicit add-Haar measure on the
target model space.

On the patch centered at `x`, the proof uses exactly

```text
extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm
```

on `extChartAt I x '' chartPairPatch I J f x`.  Mathlib's
`contMDiffOn_iff_of_subset_source'` supplies `ContDiffOn` on that literal set;
`EuclideanDimensionDropImageNullity` then proves its image null.  The explicit
chart-coordinate equation identifies this Euclidean image with the target
coordinates of the manifold patch.  Finally,
`VaryingTargetChartNullityAssembly` transports the countable family of patch
nullities into the requested fixed target chart.

The result works for general model-with-corners structures.  It introduces no
global extension of a chart representative and no canonical measure on the
target manifold, and it is not a full manifold Sard or regular-value theorem.
