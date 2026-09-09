# Jet nullity with classically admissible regularity loss

`firstNonzeroJet_image_null_of_classical_admissible_loss` proves zero target add-Haar measure of the first-nonzero-(i+1)-jet locus image on a critical source subset K.

It assumes global C^(k+1) regularity, 1 <= i <= k, and the explicit budget sourceDim + i <= targetDim + k + 1. Full classical critical-image nullity at every strictly lower source dimension remains a hypothesis. The finite-dimensional real inner-product, source completeness and second-countability, and target measure assumptions are exactly those in the Lean declaration.

The proof instantiates the reviewed jet induction at remaining order k+1-i. The order is positive; adding the lost i derivatives recovers the ambient order. For every strictly lower source dimension, the budget implies classical admissibility at this remaining order, so the classical induction predicate supplies the local critical-image nullity interface. No chart data or extra remaining-order nullity premise is assumed.

Observed dependencies are `SardFirstNonzeroJetInductiveLocusNullity` and `SardClassicalFiniteOrderCriticalNullityPredicate`. The intended consumer is t93A04; proposed additional consumers are t01A08, t01J04, t92J07, and t96J05. No consumer is modified or closed here.

Next combine admissible-loss induction with Taylor-surplus nullity, repair jet orders outside both ranges, and close full induction and rectangular localization. The budget is not automatic for all jets under classical ambient admissibility. This conditional theorem is not a complete rectangular Morse–Sard proof. The stop boundary is failure of the stated budget to imply lower-dimensional remaining-order admissibility, failure of the reviewed jet induction under these hypotheses, or a need for nonstandard axioms.

The source is promoted byte-for-byte from `/tmp/SardJetClassicalAdmissibleLossNullityProbe.lean`, SHA-256 `adf57a8bce66d21904f6bf2ed0c74e65732acf931f359c28008bb6319b40ed6c`. The included axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
