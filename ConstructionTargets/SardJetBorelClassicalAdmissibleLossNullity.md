# Borel classical admissible-loss jet nullity

The declaration `firstNonzeroJet_image_null_of_borel_classical_admissible_loss` proves zero target add-Haar measure of the first-nonzero-(i+1)-jet image on a critical source subset K.

It assumes global C^(k+1) regularity, 1 <= i <= k, and the explicit budget `sourceDim + i <= targetDim + k + 1`. The source and target are finite-dimensional real inner-product spaces; source completeness and second countability, target Borel compatibility, and the target add-Haar measure are retained explicitly. The induction premise is Borel-compatible classical critical-image nullity at every strictly lower source dimension.

The proof invokes the generic jet induction at remaining order k+1-i. The index bounds make this a positive finite order and recover the original regularity after adding i. For any lower-dimensional source G, the budget implies classical admissibility at the remaining order. The Borel-compatible induction predicate then supplies the exact localized nullity interface for G and the fixed target F.

Direct imports and observed uses are `SardFirstNonzeroJetInductiveLocusNullityProbe.firstNonzeroJetLocus_image_null_of_induction` and `SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension`. The older arbitrary-measurable-target induction predicate is neither assumed nor derived, and its declarations are unchanged.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 remain prospective consumers. This theorem is infrastructure, not frozen consumer uptake. Remaining rank and jet assembly interfaces must be migrated to Borel-compatible induction, that induction closed, and jet orders outside the covered analytic ranges repaired.

Provenance: byte-identical promotion of `/tmp/SardJetBorelClassicalAdmissibleLossNullityProbe.lean`, SHA-256 `0021f9d76d8aba2d586fa7a15b960197e9b5ab840052a438db025c4f41edbe69`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if the budget fails to imply lower-dimensional remaining-order admissibility, explicit Borel compatibility fails to instantiate the reviewed jet induction, or nonstandard axioms are required.
