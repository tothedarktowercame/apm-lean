# Positive-order Borel induction after jet loss

`firstNonzeroJet_image_null_of_borel_positive_order_loss` proves nullity of
the image of `firstNonzeroJetLocus f K (i + 1)`. Its hypotheses include
finite-dimensional real inner-product spaces, a Borel target with additive
Haar measure, global C^(k+1) regularity, a critical source subset K,
`1 ≤ i ≤ k`, and `sourceDim + i ≤ targetDim + k + 1`.

The induction premise is specifically
`BorelPositiveOrderCriticalNullityAtDimension` at strictly smaller source
dimensions. The proof establishes `1 ≤ k + 1 - i` from `i ≤ k` and passes
that fact at the actual induction application. The dimension budget and
strict dimension drop establish admissibility of the remaining order.
The regularity identity `(k + 1 - i) + i = k + 1` supplies the reviewed
first-nonzero-jet induction theorem's input.

The observed dependencies are the positive-order predicate and
`firstNonzeroJetLocus_image_null_of_induction`. No conversion to the broader
all-orders predicate is assumed or proved. This migrates the derivative-loss
jet branch only; it does not remove the budget or induction hypotheses.

The source matches `/tmp/SardJetBorelPositiveOrderLossNullityProbe.lean`,
SHA-256 `482f6c1d8c2130a00bac510bff9a68a1e40d4f40ddfef60f8de097abe021ab1f`.
Its axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Intended consumers are t93A04 and shared Sard foundations for t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is closed here. Integration
into rank-zero aggregation, migration of the rank-reduction induction
interface, and complementary analytic cases remain before rectangular
closure. The ledger and frozen consumer are unchanged.

The boundary would be failure of remaining-order positivity, lower-dimensional
admissibility, the reviewed jet induction theorem under its hypotheses, or
a requirement for nonstandard axioms.
