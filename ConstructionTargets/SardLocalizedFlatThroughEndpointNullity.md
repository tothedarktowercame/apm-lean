# Localized flat-through endpoint nullity

`localized_flatThrough_endpoint_image_addHaar_eq_zero` proves that the image
of `flatThrough f K (k + 1)` has zero measure for any target add-Haar measure.
It assumes compactness of K, global C^(k+1) regularity, and exact equality
`(k + 1) * finrank F = finrank E`. The source and target are nontrivial
finite-dimensional real inner-product spaces with Borel measurable
structures; `ProperSpace E` is retained.

The flat-through locus is specifically of order k+1, not k. Compactness of
this locus follows from the banked compact-localization theorem, using an
enclosing ball obtained from compactness of K. Its defining derivative
vanishing conditions supply normalized endpoint volume nullity. The banked
volume-to-add-Haar theorem then transfers the conclusion.

Observed imports are `SardCompactFlatEndpointNormalizedNullity`,
`SardFlatThroughCompactLocalization`, and `SardVolumeNullityToAddHaar`.
The source is byte-identical to the accepted fixture
`/tmp/SardLocalizedFlatThroughEndpointNullityProbe.lean`, SHA-256
`b06f275526d83039374157d077ad4e937286e9083c60514441853a9537fe2fb9`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

The intended consumer is t93A04; further proposed consumers are t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is modified or closed here.
Remaining work is to combine this endpoint branch with the remaining
finite-order jet branches, then complete local induction and compact
exhaustion.

The stop boundary is failure of compactness of the exact locus under these
hypotheses, failure of add-Haar nullity transfer, or a need for nonstandard
axioms. Missing downstream assembly is not a mathematical refutation.
