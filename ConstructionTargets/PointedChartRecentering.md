# Positive affine recentering of pointed charts

This target constructs a pointed chart at an arbitrary point of an existing
one-dimensional chart, inside a requested ambient open set. Its coordinate
embedding into the original chart is a positive affine map and strictly
preserves order. The Circle specialization places a recentered chart at an
actual overlap point inside both rotated-chart neighborhoods.

## Coordinate and chart construction

Given a model point `v : D` and a positive radius `r` whose Euclidean ball
lies inside the model unit disk, `ballSubtype` identifies that Euclidean ball
with the metric ball about `v` in the subtype `D`. `affineBall` composes this
identification with the unit-ball-to-ball homeomorphism. Its underlying
coordinate formula is `u ↦ r • u + v`.

For a geometric `PointedModelChart c`, `recenteredChart c v r hr hs` has
neighborhood `c.ambient '' Metric.ball v r`. Openness follows from the open
mapping property of `c.ambient`. Its coordinate homeomorphism combines
`affineBall` with the homeomorphism onto this image supplied by the ambient
embedding. The origin equation proves that it is pointed at `c.ambient v`.

`recentered_ambient_formula` gives the exact ambient equality

```text
(recenteredChart c v r hr hs).ambient u
  = c.ambient (affineBall v r hr hs u).1.
```

`recentered_coordinate_increasing` proves strict increase of the affine
coordinate embedding: `r * coord u + coord v` is strictly increasing because
`r > 0`. These constructions require a topological space and geometric
pointed-chart data; they assume no homology or orientation conclusion.

## Radius selection and Circle consumer

`exists_recenter_radius` takes an open set `U` containing `c.ambient v`.
It chooses one radius from openness of the preimage of `U` and another from
openness of the model disk, then takes their minimum. The result is positive,
its Euclidean coordinate ball lies in the model disk, and its ambient image
lies in `U`.

`exists_recentered_chart` uses that radius to construct a chart pointed at
`c.ambient v`, with neighborhood contained in both `U` and `c.neighborhood`.
`circle_overlap_recenter` specializes to rotated Circle charts at `x` and
`y`: given a coordinate point of the first lying in the second neighborhood,
it constructs a pointed chart at that overlap point inside both.

## Evidence and remaining order comparison

The Lean file is a byte-for-byte promotion of
`/tmp/PointedChartRecenteringProbe.lean`, SHA-256
`28b272797d8fcd7d62ade1407ce6795e136bdcb85e85d26666bd9232844742c2`.
All six retained axiom audits permit only `propext`, `Classical.choice`, and
`Quot.sound`. The rotated-chart dependency is committed at
`8554a6d05a1ed35d31532395c45e837818c1dbcf`, independently reviewed PASS by
`codex-11` in `invoke-1788972105766-16627-392f928f`.

The observed consumer is the rotated-Circle overlap recentering theorem.
Named downstream consumers are `oriented-circle-chart-naturality`,
`circle-fundamental-class`, and `one-manifold-chart-recentering`. No frozen
problem is changed and the placeholder delta is zero.

Next prove geometric order preservation of the transition from this common
restriction into the second rotated chart, including its recentering, and
combine it with the banked unique-global-generator localization equations.
The positive affine embedding into the first chart does not prove that
second transition is positive. No geometric compatibility is inferred from
homology equality, no additional homological existence theorem is needed,
and the parent orientation packet remains incomplete.
