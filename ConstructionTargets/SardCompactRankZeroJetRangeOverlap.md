# Compact rank-zero nullity under jet-range overlap

`compact_rankZero_image_zero_of_jet_range_overlap` proves zero target add-Haar measure of the image of a compact rank-zero set K without supplied jet-image nullity premises.

It retains global C^(k+2) regularity, classical admissibility, full lower-dimensional classical nullity, and the additional bound sourceDim + floor((sourceDim - 1) / targetDim) <= targetDim + k + 3. The nontrivial finite-dimensional real inner-product, Borel, and proper-source hypotheses are exactly those in the Lean declaration.

The proof uses the reviewed double-uncovered assembly. Failure of Taylor surplus bounds the jet order j by floor((sourceDim - 1) / targetDim), using positive target dimension. The overlap bound then contradicts failure of the admissible-loss budget. Thus no jet satisfies both uncovered inequalities.

The observed dependency is `SardCompactRankZeroDoubleUncoveredAssembly`. The intended consumer is t93A04; proposed additional consumers are t01A08, t01J04, t92J07, and t96J05. No consumer is modified or closed here.

The remaining work is to use this regime in induction and exhaustion, repair the complementary regularity range, and close full lower-dimensional induction before rectangular localization. The overlap bound is an additional restriction, not a consequence claimed for every classically admissible order. This conditional theorem is not a general rectangular Morse–Sard proof. The stop boundary is failure of the overlap bound to exclude the simultaneous uncovered inequalities, failure of the reviewed compact assembly under these hypotheses, or a need for nonstandard axioms.

The source is promoted byte-for-byte from `/tmp/SardCompactRankZeroJetRangeOverlapProbe.lean`, SHA-256 `306332ce8be2e23b0516e8f3064d610736e81e3c7e82778f8c6c1e5228360e63`. Its included axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
