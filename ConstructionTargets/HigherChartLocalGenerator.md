# Higher-dimensional chart-local generators

For every `k : ℕ`, this module constructs an integral local homology generator
in degree `k + 2` at a specified point of a T1 space charted on
`EuclideanSpace ℝ (Fin (k + 2))`. The map from the punctured model pair to
the ambient deleted-point pair is the actual chart map followed by subtype
inclusion. Its induced homology map is proved to be an isomorphism.

The construction uses `TopologicalSpace M` and `ChartedSpace (E k) M`.
The isomorphism and generation theorems additionally use `T1Space M` for
excision. No differentiability, compactness, global orientation, supplied
chart-pair equivalence, or assumed local homology isomorphism is required.
Coefficients remain integral in the production `RelativeSingularChains`
representation in `AddCommGrpCat` throughout.

Openness of the target of `chartAt (E k) x` supplies a positive radius whose
ball about the coordinate of `x` lies in that target. Restricting the inverse
chart to this ball gives an open neighborhood of `x`. Positive scaling and
translation send the model unit disk to this ball. Composing with the
restricted inverse chart defines `modelChart`, with ambient formula

```text
u ↦ (chartAt (E k) x).symm (chartRadius x • u + chartAt (E k) x x).
```

`modelChart_origin` proves that the model origin maps to `x`.
Injectivity then proves `modelChart_deletedPoint_iff`, identifying the model
puncture with the neighborhood minus `x`.

`ambientChartMap_chain_eq` identifies the relative chain map of the actual
ambient map with the chart-pair map followed by neighborhood inclusion.
`ambientChartMap_excision_chain_eq` further identifies that inclusion with
the canonical double-complement subtype identification followed by production
`relativeExcisionMap`. All these maps run forward, from the model pair into
the ambient deleted-point pair.

For an open neighborhood containing `x`, its closed complement lies inside
the interior of the ambient deleted-point set; the latter is open by T1.
Production excision and pair-homeomorphism transport therefore prove
`neighborhoodInclusion_Hn_isIso` and `ambientChartMap_Hn_isIso` in degree
`k + 2`.

`ambientLocalGenerator x` is the image of
`HigherModelLocalHomology.generator k` under this actual induced map.
Applying its inverse to an arbitrary ambient local class, using model
generation, and mapping back proves `ambientLocalGenerator_generates`.
The exact equation `ambientLocalGenerator_eq_inclusion_transport` identifies
the class with neighborhood inclusion applied to the chart-transported model
generator. Euclidean dimension-two and dimension-four instances compile.

This is a local calculation. Coordinate-change signs, compatibility of
different chart choices, coherent global orientation, fundamental classes,
localization monicity, and t98A02 gluing remain separate obligations.

The Lean file is an unchanged promotion of
`/tmp/HigherChartLocalGeneratorProbe.lean`, SHA-256
`88a76ee4d496073f92f963aed331c56283e99a2c119a47ba1f046e1c469244c3`.
The model dependency was independently reviewed PASS at commit
`ab4cc42e6c62e20c2c6e9a3778c9916433c598a4`.
Validation compiles the fixture and canonical target, builds this module
with `HigherModelLocalHomology` and `OneDimensionalChartLocalGenerator`,
and reproduces all nine printed axiom audits and recorded statement hashes.
The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
