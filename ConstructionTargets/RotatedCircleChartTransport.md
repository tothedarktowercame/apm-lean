# Constructed rotated Circle charts and localization

This target constructs a pointed chart at each Circle point by rotating the
fixed chart at `1`. It identifies the chart's actual relative chain map and
local class with fixed-chart transport followed by rotation. The previously
normalized absolute class therefore localizes to these constructed chart
classes at every point.

## Geometric construction and exact comparison

`rotatedChart x` takes its neighborhood to be the image of
`(constructedChart 1).neighborhood` under `Homeomorph.mulLeft x`. The image is
open, and the coordinate homeomorphism is the fixed chart's coordinates
followed by the rotation homeomorphism restricted to that neighborhood.
The origin equation follows from the fixed chart's origin equation and
`x * 1 = x`.

The source representation is the production model-to-Circle relative
singular chain map of this constructed pointed chart. The target is the
fixed chart's relative chain map followed by the relative map induced by
rotation from the pair deleted at `1` to the pair deleted at `x`.

The direction is exact equality from the constructed chart map to the
fixed-chart-then-rotation composite. `rotatedChart_ambient` proves this first
for the continuous ambient maps. `rotatedChart_chain_map` proves it for the
production relative chain maps using `relativeSingularMap_comp`.
`rotatedChart_localClass` applies homology composition to identify the
constructed chart's local class with `rotatedLocalClass x`.

All absolute and relative homology groups use integral production singular
chains in `AddCommGrpCat`; no coefficient or representation substitution is
made.

## Localization and uniqueness

`globalClass_localizes_chart` combines the proved class identification with
the rotation/localization square to obtain

```text
∀ x : Circle, localization x globalClass = (rotatedChart x).localClass.
```

`rotatedChart_one_localClass` identifies the rotated chart's class at `1`
with the original chart's class there. `unique_global_chart_class` proves
there exists exactly one absolute integral `H₁` class which generates the
whole group and satisfies all these constructed-chart localization equations.
Existence uses `globalClass`; uniqueness follows by specializing the equations
at `1` and applying the inverse of actual localization.

## Evidence and geometric boundary

The Lean file is a byte-for-byte promotion of
`/tmp/RotatedCircleChartTransportProbe.lean`, SHA-256
`80fb4ce21a5c498bbac7644e31a6f575edd67b0f1910b6e2e111bf77ba183622`.
All six retained axiom audits permit only `propext`, `Classical.choice`, and
`Quot.sound`. The rotation/localization prerequisite is committed at
`b349ae35bc82e42b0ead8623710e2375abd29275`, independently reviewed PASS by
`codex-11` in `invoke-1788971690326-16618-250b231c`.

The observed consumer is the unique class satisfying every constructed-chart
localization equation. The named downstream consumers are
`circle-fundamental-class`, `circle-degree-localization`, and
`oriented-circle-chart-naturality`. No frozen problem is changed and the
placeholder delta is zero.

Geometric coordinate-order compatibility of these charts on constructed
common restrictions remains to be proved, including recentering when charts
have different centers. Equality of homology classes does not establish that
geometric condition. This packet claims neither the full parent orientation
packet, higher-dimensional results, nor closure of `t98A02`.
