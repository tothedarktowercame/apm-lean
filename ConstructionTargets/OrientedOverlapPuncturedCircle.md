# Oriented overlap and punctured-circle local homology

This target constructs a common restriction of two pointed open one-disk
charts, proves equality of their ambient local classes under a geometric
positive-transition hypothesis, and computes the positive-degree integral
homology of the circle with any specified point removed. All homology uses
the production integral singular representation in `AddCommGrpCat`.

## Constructed common restriction

`scale r hr hr1` multiplies model coordinates by `r`, for `0 < r ≤ 1`.
`scale_increasing` proves strict coordinate increase. For a geometric
`PointedModelChart c`, `smallNeighborhood c r` is the ambient image of its
coordinate ball of radius `r`. Its openness follows from the chart's open
mapping property.

`shrinkCoordinates` constructs a homeomorphism from the model disk onto this
smaller neighborhood, with inverse obtained by reading the old coordinates
and scaling by `r⁻¹`. `shrinkChart` packages it as a pointed chart.
`shrink_transition` identifies the transition into the original chart with
positive scaling, so `shrink_compatible` proves compatibility geometrically.

For charts `c` and `d` at the same point, `exists_common_radius` applies
openness to the preimage of `d.neighborhood` under `c.ambient` and chooses a
positive radius at most one. `commonChart` restricts `c` by that radius. Its
neighborhood lies inside both charts, and `common_ambient_maps` proves that
both transitions commute with the same ambient map.

`OrientedCompatible c d` means strict increase of the actual transition from
this constructed common chart into `d`. The transition into `c` is already
proved increasing by scaling. The banked nested-chart homology square then
gives `oriented_overlap_localClass_eq : c.localClass = d.localClass`.
The common restriction is constructed here; positivity of the transition
into the second chart is the geometric compatibility hypothesis, not an
assumed homology sign or class equality. Overlap equality needs only the
topological space and these pointed chart data.

`circle_half_chart_overlap` specializes to the constructed Circle chart and
its half-radius restriction. `half_neighborhood_ne` proves that these are
distinct neighborhoods by exhibiting a point at coordinate norm `3/4` that
cannot lie in the half-radius image. Their classes agree in ambient local
`H₁`.

## Punctured circle and actual homology comparison

`puncturedCircleToMetric` restricts the existing Circle/metric-circle
homeomorphism away from the specified point. `puncturedCircleLine` composes
this with stereographic projection restricted to its actual source and
target, then with the real-line coordinate homeomorphism. Thus
`Circle ∖ {x}` is explicitly homeomorphic to `ℝ` for every `x : Circle`.

`puncturedCircleHomologyIsoLine` applies the integral singular homology
functor to that homeomorphism. `puncturedCircleHomologyIsoLine_hom` identifies
its forward map with the map induced by the exhibited continuous map.
`puncturedCircle_positive_homology` transports contractibility from `ℝ` and
proves that the punctured circle's homology is zero for every `n ≠ 0`.

`circle_relative_generator` proves that the constructed chart's ambient
relative class generates all of `H₁(Circle, Circle ∖ {x}; ℤ)`.
`circle_relative_generator_comparison` identifies that class exactly with
production chart-pair transport followed by actual neighborhood inclusion,
whose excision comparison is banked. Generator preservation uses the T1
neighborhood-excision theorem; Circle satisfies its hypotheses.

## Evidence and boundary

The Lean file is a byte-for-byte promotion of
`/tmp/OrientedOverlapPuncturedCircleProbe.lean`, SHA-256
`48cfa5e5c5b2552c6b7109e43def8f77f0ad7d6824954246da357d353b7dedee`.
All eleven retained axiom audits permit only `propext`, `Classical.choice`,
and `Quot.sound`. The nested-chart prerequisite is committed at
`77786b3c35ec70eb3e6674b385dca0ef0af706dd`, independently reviewed PASS by
`codex-11` in `invoke-1788968788804-16538-2ea5c13a`.

The observed consumers are the distinct Circle chart comparison,
punctured-circle vanishing, and the relative generator comparison. They
fulfill this row's `circle-local-orientation-overlap` and
`punctured-circle-local-homology` tasks. No frozen problem is changed and the
placeholder delta is zero. A global fundamental class, general top-homology
localization monicity, and closure of `t00J02` are not consequences claimed
by this one-dimensional packet.
