# Neighborhood inclusion and local homology excision

This target identifies the actual neighborhood-inclusion relative chain map
with production excision and proves that it preserves integral local `H₁`
generators. For a T1 space `X`, an open subset `U`, and `x ∈ U`, the induced
map from `H₁(U, U ∖ {x}; ℤ)` to `H₁(X, X ∖ {x}; ℤ)` is an isomorphism.
The representation is production relative singular chains in `AddCommGrpCat`.

## Exact representation comparison

The source is the relative singular-chain map of the actual subtype inclusion
`neighborhoodInclusion U : C(U, X)`, from the pair
`(U, neighborhoodDeletedPoint U x)` to `(X, deletedPoint x)`.

The target is the composite of the relative map of
`neighborhoodExcisionHomeomorph U : U ≃ₜ ((Uᶜ)ᶜ : Set X)` with
`relativeExcisionMap (deletedPoint x) Uᶜ`. The homeomorphism comes from double
complement equality; `neighborhoodExcision_pair_iff` proves its pair witness.

The direction is exact equality from the actual neighborhood-inclusion chain
map to this canonical identification followed by production excision.
`neighborhoodInclusion_chain_eq` proves that equality using
`relativeSingularMap_comp` and equality of the underlying composite with
subtype inclusion. Both sides therefore induce the same forward integral
local `H₁` map into `X`. This chain-map equality requires only a topological
space and the specified subset and point.

## Excision and generator preservation

`neighborhoodInclusion_H1_isIso` adds `[T1Space X]`, `IsOpen U`, and `x ∈ U`.
The T1 hypothesis makes the deleted-point set open. Openness of `U` makes
`Uᶜ` closed, and `x ∈ U` ensures `Uᶜ` lies inside the interior of the
deleted-point set. These are the hypotheses of production excision. The
canonical pair homeomorphism also induces an isomorphism, so the chain-map
comparison proves that the actual inclusion induces an isomorphism on `H₁`.

`neighborhoodInclusion_sends_generator` assumes a neighborhood local class
`g` such that every neighborhood local class is an integer multiple of `g`.
For every ambient local class `z`, it proves

```text
∃ n : ℤ, n • inclusion_*(g) = z.
```

The proof pulls `z` back through the inverse of the actual inclusion-induced
isomorphism, applies the neighborhood generation hypothesis, then maps the
result forward. It constructs neither `g` nor a chart.

`lineNeighborhoodInclusion_H1_isIso` and
`circleNeighborhoodInclusion_H1_isIso` specialize the isomorphism to the
radius-one metric ball around a point of `ℝ` and `Circle`, respectively.
These are neighborhood-excision specializations, not model-chart instances.

## Evidence, consumers, and remaining work

The Lean file is a byte-for-byte promotion of
`/tmp/LocalHomologyNeighborhoodExcisionProbe.lean`, SHA-256
`a9f4488775de93310f82273d66df283cd9ab9cfd362bc149abc7d1766d3c57e3`.
All five retained `#print axioms` checks use only `propext`, `Classical.choice`,
and `Quot.sound`. The imported model/sign dependency is committed at
`1333150cc6443e151e5df62e24d4d3ddf1417cab`, independently reviewed PASS by
`codex-11` in `invoke-1788967020931-16497-882d80a9`.

The observed consumers are generator preservation under inclusion and the
line/Circle neighborhood isomorphisms in this target. The intended downstream
consumers are `circle-chart-local-orientation` and
`euclidean-line-local-orientation`. No frozen problem is changed, and the
placeholder delta is zero.

Next construct the actual restricted pointed model-to-neighborhood chart and
its deleted-point pair equivalence on the line and Circle, transport the
banked model generator through that chart, and apply this inclusion theorem.
Supplied chart data does not constitute chart construction. This packet
claims no overlap compatibility, global fundamental class, or localization
monicity.
