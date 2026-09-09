# Actual Circle localization and pointwise normalization

For each point `x : Circle`, this target proves that the actual localization
map from absolute integral `H₁(Circle)` to relative integral
`H₁(Circle, Circle ∖ {x})` is an isomorphism. It pulls the constructed
chart-local generator back through that map and proves the resulting class
generates absolute `H₁`. The normalization is pointwise in `x`.

## Actual maps and proof

The source is `(SingularChains (TopCat.of Circle)).homology 1`; the target is
`(RelativeSingularChains (deletedPoint x)).homology 1`. Both use production
integral singular chains in `AddCommGrpCat`. The forward map `localization x`
is exactly `homologyMap (relativeSingularProjection (deletedPoint x)) 1`.

`punctureH0Inclusion_isIso` proves invertibility of the actual puncture
inclusion's `H₀` map. It uses the punctured-circle-to-line homeomorphism for
contractibility, the existing integral `H₀` isomorphisms for the puncture and
Circle, and the augmentation/naturality theorem `h0Map_isIso_of_iso_int`.
The Circle `H₀` isomorphism is imported from `BoundaryTorusMayerVietoris`.

`connecting_eq_zero` cancels this invertible inclusion map in the production
pair sequence, showing that the connecting map from relative `H₁` to
puncture `H₀` vanishes. Punctured-circle `H₁` vanishing and exactness make
`localization x` monic; the zero connecting map and exactness make it epic.
`localization_isIso` concludes that this actual map is invertible.

`localizationIso` is `asIso (localization x)`, so its forward map is the
projection-induced map just proved invertible. `localization_hom_inv` and
`localization_inv_hom` prove both categorical inverse identities. No abstract
group isomorphism is substituted for the localization map.

## Pointwise generator equations

`normalizedClass x` is the inverse image of `(constructedChart x).localClass`
under `localizationIso x`. The concrete consumer equations are

```text
localization x (normalizedClass x) = (constructedChart x).localClass
∀ z : H₁(Circle; ℤ), ∃ n : ℤ, n • normalizedClass x = z.
```

`normalizedClass_localizes` proves the first equation by the inverse identity.
`normalizedClass_generates` applies the local generator theorem to the
localization of an arbitrary absolute class, then pulls the resulting integer
multiple equality back through the inverse.

## Evidence and remaining coherence

The Lean file is a byte-for-byte promotion of
`/tmp/CircleActualLocalizationProbe.lean`, SHA-256
`69d7fb8cfdbc03f14539e0308edb02fef494113baab74e8ebb78c0f1d57592f2`.
All seven retained axiom audits permit only `propext`, `Classical.choice`,
and `Quot.sound`. The overlap/punctured-circle dependency is committed at
`487f1de0315ae18a93ffa518c74e49e2aa52c9ac`, independently reviewed PASS by
`codex-11` in `invoke-1788969590260-16560-15b330e9`.

The observed consumer is pointwise normalization for
`circle-global-local-homology`. Proposed downstream consumers are
`circle-fundamental-class` and `circle-degree-localization`. No frozen problem
is edited and the placeholder delta is zero.

Next construct a geometrically coherent rotation-oriented chart family and
prove that one global Circle class satisfies every localization equation.
The separately constructed chart signs at different points are not proved
coherent by these pointwise inverse images. No global orientation coherence,
arbitrary-manifold localization, or higher-dimensional result is asserted.
