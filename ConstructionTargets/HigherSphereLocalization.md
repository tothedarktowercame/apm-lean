# Actual localization on higher spheres

For `k : ℕ`, let `Sphere k` be the literal unit sphere in
`EuclideanSpace ℝ (Fin (k + 3))`. This module proves that its actual
absolute-to-relative integral homology map in degree `k + 2` is an
isomorphism at every specified point `x`.

`puncturedSphereEuclidean x` uses stereographic projection with pole `x`.
Its source is identified with `deletedPoint x`, and its target with the
whole of `EuclideanSpace ℝ (Fin (k + 2))`. The source and target set
equalities, followed by the universal-set subtype homeomorphism, turn the
partial stereographic map into an actual homeomorphism. The `dimension`
instance verifies the finite-dimensional hypothesis for this sphere.

`punctureHomologyIso` applies integral singular homology to that
homeomorphism. `punctureHomologyIso_hom` identifies its forward morphism
with the induced map of the actual continuous stereographic map.
Euclidean contractibility transfers to the puncture, proving
`puncture_positive_homology` in every nonzero degree.

The localization map is exactly

```lean
HomologicalComplex.homologyMap (relativeSingularProjection (deletedPoint x)) (k+2)
```

Production pair exactness and vanishing of puncture homology in degree
`k + 2` make this map monic. Vanishing in degree `k + 1` makes the
connecting morphism zero, so exactness makes localization epic. Both
degrees are positive. The resulting `localization_isIso` proves
invertibility of this specific map; `localizationIso` packages it with
`asIso`. The two lemmas `localization_hom_inv` and
`localization_inv_hom` exhibit both inverse identities.

All groups use the canonical integral singular-chain representation in
`AddCommGrpCat`, including production `RelativeSingularChains`. The
sphere's actual chart instance supplies the previously constructed
`HigherChartLocalGenerator.ambientLocalGenerator x`.
`normalizedClass x` is its inverse image under localization. Thus

```text
localization x (normalizedClass x) = ambientLocalGenerator x.
```

To prove generation, localize any absolute class, express it as an integer
multiple of the chart-local generator, and apply the inverse map.
`normalizedClass_generates` gives the resulting integer multiple equation.
The dimension-two and dimension-four localization equations compile with
the concrete sphere and chart instances.

Normalization is pointwise: this module does not compare independently
chosen chart signs or normalized classes at different points. Coordinate
changes, coherent global orientation, arbitrary-manifold localization
monicity, and t98A02 gluing remain separate obligations.

The Lean source is an unchanged promotion of
`/tmp/HigherSphereLocalizationProbe.lean`, SHA-256
`99f41f8ce9bea78f25b5738c4d28d42536fc7e9f7d44d7b65cb078d51b9b5ed6`.
The chart-generator dependency was independently reviewed PASS at commit
`263ab681b5047a379c3fd1ec1378c8aefefdcd4d`.
Validation compiles the fixture and canonical target, builds this module
with `HigherChartLocalGenerator` and `HigherModelLocalHomology`, and checks
all ten recorded statement hashes and printed axiom audits. The permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`.
