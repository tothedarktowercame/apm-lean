# Finite intrinsic Hausdorff measure on low-dimensional spheres

For `d : ℕ` with `d ≤ 3`, this module proves finite `d`-dimensional
Hausdorff measure on the literal unit sphere subtype in
`EuclideanSpace ℝ (Fin (d + 1))`. Finiteness follows from an explicit
finite cap cover, using the previously constructed cap maps and their
finite intrinsic image measures.

`in_cap` reconstructs a unit vector `x` whose inner product with a unit
pole `e` is at least `1/2`. Set `t = inner ℝ x e` and `u = x - t • e`.
Then `u` is orthogonal to `e`, its norm is at most `9/10`, and
`height u = t`. Thus the actual radius-`9/10` cap map sends `u` to `x`,
with equality in the sphere subtype.

For `d ≤ 3`, the sum of squared coordinates proves that some coordinate
of every sphere point has absolute value at least `1/2`. The poles are
the positive and negative coordinate unit vectors, indexed by
`Fin (d + 1)` and `Bool`. Choosing the coordinate's sign and applying
`in_cap` proves `caps_cover`: the union of these actual cap images equals
the entire sphere. The cap measure estimate uses radius `9/10` and
positive height bound `1/4`, satisfying all previously required inequalities.

`sphere_measure_finite` takes two finite unions of the finite cap-image
bounds. `sphere_isFiniteMeasure` packages the result for intrinsic
`Measure.hausdorffMeasure d` on the sphere subtype. Compactness then gives
`continuous_integrable` for every continuous real function on that sphere.
No finite-measure assumption or radial-measure identification enters this
proof.

The consumer specializations establish integrability of the exact flux
polynomial on the two-sphere,

```text
u₀ (u₀+c₀-1)³ + u₁ (u₁+c₁-2)³ + u₂ (u₂+c₂-3),
```

and of the mixed and square terms `x₁³ x₀` and `x₀²` on the three-sphere.
`unitFlux_split` justifies addition of the three flux integrals.
`projective_density_split` justifies subtraction and constant multiplication
for the density `x₁³ x₀ - 4 x₀²`. These equations concern the literal
intrinsic Hausdorff integrals.

The primary Lean file is an unchanged promotion of
`/tmp/IntrinsicSphereFiniteProbe.lean`, SHA-256
`f8ed178719b52dfe6b8d67310b3084f0f1bc809b7fc9887fbc89a9c06dd61f8b`.
The separate temporary consumer audit
`/tmp/IntrinsicSphereConsumerAudit.lean`, SHA-256
`8c3ec6cabc306ae8cf2ec22a5924b9209aad97d05991df8c6172ed050ab6f828`,
checks the applications against `T02A05Diagnostic.unitFlux` and
`t95J05InclusionPullback`. It is not promoted into the canonical module.
The cap-finiteness dependency was independently reviewed PASS at
`c57f09381088e06fc9b385b83354f2e9decf7567`.

Validation compiles the primary fixture and canonical module, builds this
module with `SphereCapFiniteMeasure` and `SphereCapGraph`, and reproduces
the ten printed axiom audits. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. The consumer audit has three existing
`unnecessarySimpa` warnings in diagnostic proofs.

Numerical Hausdorff normalization, comparison with radial measure, and
moment evaluation remain downstream. Neither frozen integration consumer
is closed by this integrability result, and the stopped full comparison is
not retried here.
