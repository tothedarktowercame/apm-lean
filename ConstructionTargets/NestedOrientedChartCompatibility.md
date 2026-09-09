# Nested oriented charts determine equal ambient local classes

This target constructs the coordinate transition between pointed charts on
nested neighborhoods and proves equality of their ambient integral local
`H₁` classes when that transition is strictly increasing. It also proves the
corresponding consequence for a supplied common nested chart.

## Geometric data and actual maps

`PointedModelChart x` contains only an open neighborhood, a homeomorphism
from the pointed open one-disk to that neighborhood, and proof that the model
origin maps to `x`. `puncture_iff` derives the deleted-point pair witness.
`ambient` composes the coordinate homeomorphism with actual neighborhood
inclusion, and `localClass` is the image of the banked model generator under
its production relative singular `H₁` map. The representation is integral
`RelativeSingularChains` in `AddCommGrpCat` throughout.

For `h : c.neighborhood ⊆ d.neighborhood`, `transition c d h` is the continuous
map from the model disk to itself obtained by applying `c.coordinates`, the
subtype inclusion into `d.neighborhood`, and `d.coordinates.symm`.
`transition_origin` proves that it fixes the origin. `ambient_transition`
proves the exact continuous-map equality

```text
d.ambient.comp (transition c d h) = c.ambient.
```

`Compatible c d h` means strict coordinate increase of this constructed
transition. It assumes no equality of local classes or sign of a homology
map. The transition need not be a surjective self-homeomorphism of the disk.

## Homology comparison and generators

`transition_homology_square` applies production relative-map composition to
the actual transition and ambient maps. The increasing-map theorem supplies
its deleted-origin witness. Evaluating the resulting square on the model
generator and applying the banked geometric increasing-map computation gives
`compatible_localClass_eq : c.localClass = d.localClass`.

`localClass_generates` additionally assumes `T1Space M`. Pair-homeomorphism
transport sends the model generator to a neighborhood generator, and the
proved neighborhood-excision inclusion sends that generator into ambient
local `H₁`. Every ambient local class is therefore an integer multiple of
`c.localClass`.

For a space charted over Euclidean one-space, `constructedChart` uses the
banked restricted chart construction to supply the geometric record.
`constructedChart_localClass` identifies its class with the existing
`ambientLocalGenerator` by exact equality.

`localClass_eq_of_common_nested_chart` takes a common pointed chart, its two
neighborhood inclusions, and proofs that both constructed transitions are
increasing. Two applications of nested compatibility give equality of the
original charts' classes in the same ambient local homology group.

## Evidence and remaining construction

The Lean file is a byte-for-byte promotion of
`/tmp/NestedOrientedChartCompatibilityProbe.lean`, SHA-256
`d6a320fc64a7b85cee13c6346bf165425a619d9dba2e6a7d74d633cd0ede7fbb`.
All seven retained axiom audits permit only `propext`, `Classical.choice`,
and `Quot.sound`. The chart-local-generator dependency is committed at
`80e84e8694036cf750564b74a1496b83e71a5c04`, independently reviewed PASS by
`codex-11` in `invoke-1788968233457-16524-d58cdcdf`; the model/sign dependency
is `1333150cc6443e151e5df62e24d4d3ddf1417cab`.

The observed consumers are the constructed-chart class identification and
the conditional common-chart consequence. Named downstream consumers are
`circle-local-orientation-overlap` and `punctured-circle-local-homology`.
No frozen problem is changed and the placeholder delta is zero.

The common chart is an input here. Constructing a common restriction for
overlapping oriented charts, verifying its two increasing transitions, and
instantiating distinct overlapping Circle charts remain downstream. The
parent probe also retains the punctured-circle-to-line homeomorphism,
positive-degree integral homology vanishing, and local-generator comparison.
This packet completes none of those tasks and implies no global fundamental
class or localization monicity.
