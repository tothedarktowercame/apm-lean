# Constructed one-dimensional charts and ambient local generators

This target constructs a pointed chart from the open Euclidean one-disk to a
neighborhood of a specified point, proves its deleted-point pair equivalence,
and sends the model generator into ambient integral local `H₁` through the
actual chart and neighborhood inclusion. It supplies concrete Euclidean
one-space, real-line, and Circle instances.

## Hypotheses and chart construction

The construction assumes `TopologicalSpace M` and
`ChartedSpace (EuclideanSpace ℝ (Fin 1)) M`. `T1Space M` is additionally
required for neighborhood excision and the generator theorem. No
differentiability, global orientation, fundamental class, or localization
injectivity is assumed. Homology uses production integral
`RelativeSingularChains` in `AddCommGrpCat` throughout.

Starting with `chartAt E x`, `exists_chart_radius` selects a positive radius
whose ball about the coordinate of `x` lies inside the chart target.
`restrictedInverseChart` restricts the inverse chart to this ball, and
`chartNeighborhood` is its open target. `modelChart` translates and rescales
the unit disk to the selected ball, identifies it with the restricted
inverse chart's source, and applies that inverse chart.

`modelChart_origin` proves that the origin maps to `x`.
`modelChart_deletedPoint_iff` uses this equality and homeomorphism injectivity
to identify the punctured model with the deleted-point neighborhood. Thus the
chart and its pair witness are constructed from the atlas, not supplied as
additional hypotheses.

## Exact map comparison and generator

The source representation is integral relative singular `H₁` of the pointed
open one-disk model. The target is integral relative singular `H₁` of `M`
relative to the complement of `x`.

The direction is model to ambient space: `ambientChartMap_chain_eq` identifies
the induced chart-to-ambient chain map exactly with the constructed
chart-pair map followed by actual neighborhood inclusion. Pair-homeomorphism
transport and neighborhood excision then prove `ambientChartMap_H1_isIso`.

`ambientLocalGenerator` is the image of
`openDiskOnePunctureRelativeH1Generator` under this actual induced map.
`ambientLocalGenerator_generates` proves every ambient local class is an
integer multiple of that image, by pulling the class back through the proved
isomorphism and using the model's integer coordinates.
`ambientLocalGenerator_eq_inclusion_transport` additionally gives the exact
class equality with neighborhood inclusion applied to production
`transportedOpenDiskOnePunctureGenerator`.

## Concrete consumers and evidence

`euclideanLine_local_generator` uses the Euclidean one-space atlas.
`circle_local_generator` uses the existing Circle atlas.
For literal `ℝ`, `realLineCoordinates` constructs the coordinate
homeomorphism into Euclidean one-space, and `realLineAtlas` supplies its
single-chart atlas locally. `realLocalGenerator` and
`realLine_local_generator` use that explicit atlas without replacing a global
instance.

These concrete generator equations are observed consumers in this packet.
The named campaign consumers are `circle-chart-local-orientation` and
`euclidean-line-local-orientation`; overlap compatibility remains downstream.

The Lean file is a byte-for-byte promotion of
`/tmp/OneDimensionalChartLocalGeneratorProbe.lean`, SHA-256
`44459f5d5ebdc8fad706447b56335012767955043a440536f7aefa5f1940598a`.
All eleven printed axiom audits permit only `propext`, `Classical.choice`, and
`Quot.sound`; all eight recorded statement hashes are preserved.
The reviewed dependencies are model/sign commit
`1333150cc6443e151e5df62e24d4d3ddf1417cab` and neighborhood-excision commit
`3dc832fc33991b0a7b387743e7c1ab784f255d51`, independently passed by `codex-11`
in `invoke-1788967020931-16497-882d80a9` and
`invoke-1788967616833-16511-ed8e0652`, respectively.

No chart-local-generator proof residual remains in this row. The next row
must establish oriented overlap equality and the punctured-circle comparison.
No frozen problem is changed, and the placeholder delta is zero. These local
constructions imply neither arbitrary-dimensional model homology nor a global
fundamental class or localization monicity.
