# Quantitative sphere-cap graph

This module constructs a Lipschitz map from an orthogonal disk into the
literal unit sphere subtype and bounds the Hausdorff measure of its image.
The ambient space `E` is a real inner-product space; finite dimension and
completeness are not required for these estimates.

The explicit formulas are

```text
height u = sqrt (1 - ‖u‖²)
graph e u = u + height u • e.
```

For `0 ≤ r < 1`, `a > 0`, and `a² ≤ 1 - r²`, the height is at least `a`
on the closed radius-`r` ball. Factoring the difference of squared heights
and using the reverse triangle inequality proves `height_difference`:

```text
|height u - height v| ≤ (r/a) * ‖u-v‖.
```

When `‖e‖ = 1`, the triangle inequality gives `graph_lipschitz` with
constant `1 + r/a` on that whole closed ball. Orthogonality is additionally
used in `graph_norm`: if `inner ℝ u e = 0`, the graph has norm one.

`capDomain e r` is the actual subtype
`{u : E // ‖u‖ ≤ r ∧ inner ℝ u e = 0}`. The norm calculation defines
`capMap` from this domain into `Metric.sphere (0 : E) 1`.
`capMap_lipschitz` proves the same constant for the subtype metrics.

With a Borel measurable structure on `E`, for every real `d ≥ 0`,
`capMap_hausdorff_bound` applies the Lipschitz Hausdorff image inequality:

```text
hausdorffMeasure d (range capMap)
  ≤ (1 + r/a)^d * hausdorffMeasure d univ.
```

The left measure is on the sphere subtype and the right measure is on
`capDomain e r`, with the constant coerced to extended nonnegative reals.
The right-hand side may be infinite. The result does not assume or prove
finite measure of the domain or sphere.

The remaining consumer work is to identify the domain isometrically with a
compact ball in a finite-dimensional hyperplane and prove finite
top-dimensional Hausdorff measure there. One must then construct finitely
many signed coordinate caps covering spheres of dimensions two and three,
sum these bounds, and derive the exact frozen polynomial-integrability
instances. Finite coverage, intrinsic sphere finiteness, measure
normalization, and numerical moments are not established in this module.

The Lean source is an unchanged promotion of
`/tmp/SphereCapGraphProbe.lean`, SHA-256
`e39cf758629bb44251562af80de0641daa47d9f6b6f61db26e991f2e9a5df7af`.
This row has no ledger dependencies and imports Mathlib directly.
Validation compiles the fixture and canonical target, runs
`lake build ConstructionTargets.SphereCapGraph`, and audits all six printed
declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted axioms.
