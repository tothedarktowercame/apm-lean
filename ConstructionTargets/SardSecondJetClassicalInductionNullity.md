# Second-jet nullity from classical induction

`secondJet_image_null_of_classical_lowerDimension_induction` proves zero target add-Haar measure of the first-nonzero-second-jet locus image on a critical source subset K.

The hypotheses retain global C^(k+2) regularity, classical Sard admissibility at order k+2, and full classical critical-image nullity at every strictly lower source dimension. The finite-dimensional real inner-product, source completeness and second-countability, and target measure structures are exactly those in the Lean statement.

The proof specializes the reviewed first-nonzero-jet induction theorem to i = 1 and remaining order k+1. At any strictly lower source dimension, classical admissibility at the ambient order implies admissibility at this remaining order. Thus the full classical lower-dimensional predicate supplies the required local nullity interface. No chart data, Taylor surplus, or additional remaining-order nullity premise is assumed.

Observed dependencies are `SardFirstNonzeroJetInductiveLocusNullity` and `SardClassicalFiniteOrderCriticalNullityPredicate`. The intended consumer is t93A04; proposed additional consumers are t01A08, t01J04, t92J07, and t96J05. No consumer is closed or modified here.

Next integrate this second-jet case into uncovered-jet assembly, discharge remaining uncovered orders j >= 3, close full lower-dimensional induction, and remove global regularity through rectangular localization. This conditional second-jet theorem does not establish the full induction hypothesis or rectangular Morse–Sard. The stop boundary is failure of admissibility after one derivative of loss at strictly lower source dimension, failure of the reviewed jet induction under these hypotheses, or a need for nonstandard axioms.

The Lean source is promoted byte-for-byte from `/tmp/SardSecondJetClassicalInductionNullityProbe.lean`, SHA-256 `ad8e9c1983b84f95318cdcf687f871c3539f8c77876c8eaa0e566689b4246e11`. Its included axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
