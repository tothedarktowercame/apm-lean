# Compact rank-zero assembly outside both covered jet ranges

`compact_rankZero_image_zero_of_double_uncovered_jets` proves zero target add-Haar measure of the image of a compact rank-zero source set K.

It retains global C^(k+2) regularity, classical Sard admissibility, and full lower-dimensional classical nullity. Explicit jet-image nullity is required only for 3 <= j <= k+2 satisfying both j * targetDim <= sourceDim - 1 and targetDim + k + 2 < sourceDim + (j - 1). The nontrivial finite-dimensional real inner-product, Borel, and proper-source hypotheses are exactly those in the Lean statement.

The reviewed third-jet assembly already handles second jets and Taylor-surplus orders. The new proof splits the remaining orders by the admissible-loss budget. Rank zero implies criticality for a nontrivial target, enabling the admissible-loss theorem at i = j - 1. The predecessor identity restores the required jet index. Only orders outside both covered ranges are passed to the explicit nullity hypothesis.

Observed dependencies are `SardCompactRankZeroThirdJetAssembly` and `SardJetClassicalAdmissibleLossNullity`. The intended consumer is t93A04; proposed additional consumers are t01A08, t01J04, t92J07, and t96J05. No consumer is modified or closed here.

The residual is to prove jet nullity in the intersection of the two uncovered ranges, close full lower-dimensional induction, and complete exhaustion and rectangular localization. This is conditional assembly, not a full rectangular Morse–Sard theorem. The stop boundary is failure of admissible-loss nullity to discharge covered orders, failure of rank-zero criticality under the stated target assumptions, or a need for nonstandard axioms.

The source is promoted byte-for-byte from `/tmp/SardCompactRankZeroDoubleUncoveredAssemblyProbe.lean`, SHA-256 `355011ff7ff2726855000e7eda509977d72d5cd67a0d353b81331fedc88c55a5`. The included axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
