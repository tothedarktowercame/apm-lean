# Compact flat endpoint nullity

`compact_flat_endpoint_volume_eq_zero` proves zero target volume of the image
of a compact bounded source locus. The real inner-product source and target
are finite dimensional and nontrivial, with Borel measurable structures; the
source also carries `ProperSpace`. The map is globally C^(k+1), and all its
derivatives of orders 1 through k+1 vanish on the locus. The dimension
condition is the exact equality `(k + 1) * finrank F = finrank E`.
The nonzero source unit-ball volume constant is an explicit hypothesis.

For each positive volume tolerance, geometric scale selection gives a
positive Taylor coefficient whose target-dimensional power makes the volume
bound smaller than that tolerance. Compact uniform small Taylor remainders
provide its validity radius. The compact cover construction supplies the
localized finite-cover data, and localized endpoint small-coefficient nullity
then gives the conclusion.

Observed dependencies are `SardCompactUniformSmallTaylorRemainder`,
`SardLocalEndpointCompactCoverData`, and `SardNNRealGeometricScaleTolerance`.
The Lean file is byte-identical to the accepted fixture
`/tmp/SardCompactFlatEndpointNullityProbe.lean` (SHA-256
`7aadff8025f6ec44aae8d95152e99e64af70d23aa143705c7a581156694dccbb`).
Its axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

The intended consumer is t93A04; further proposed consumers are t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is changed or closed here.
Remaining work is to specialize this result to the finite-order jet
decomposition, supply source volume normalization, and complete localization,
induction, and compact exhaustion.

The stop boundary is a mathematical failure of compact flat endpoint nullity
under these hypotheses, or a need for nonstandard axioms; missing downstream
assembly is not a refutation.
