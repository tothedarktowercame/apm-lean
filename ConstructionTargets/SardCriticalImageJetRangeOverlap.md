# Critical image nullity under jet-range overlap

The declaration `criticalImage_zero_of_jet_range_overlap_induction` proves zero target add-Haar measure for the image of the nonsurjective-derivative locus intersected with any source subset.

The hypotheses retain global C^(k+2) regularity, classical Sard admissibility, full classical critical-image nullity at every strictly lower source dimension, and the overlap bound
`sourceDim + (sourceDim - 1) / targetDim <= targetDim + k + 3`.
Division is natural-number division. The Lean statement explicitly retains nontrivial finite-dimensional real inner-product source and target spaces, Borel measurable structures, and a proper source.

The proof obtains closedness of the rank-zero locus from continuous differentiability, exhausts it by compact sets using the closed-open image-nullity theorem with the whole source as the open set, and applies compact overlap nullity to each member. The finite-order critical-image assembly handles positive ranks using the lower-dimensional hypothesis. Measure monotonicity then restricts the conclusion to the supplied source subset.

The four direct imports are reviewed dependencies: compact rank-zero jet-range overlap, closed-open image nullity, derivative-rank upper-locus closedness, and finite-order critical-image assembly from rank-zero nullity. This module is intended infrastructure for t93A04; t01A08, t01J04, t92J07, and t96J05 remain prospective consumers, not established imports.

This is a conditional overlap-regime theorem, not general rectangular Morse–Sard. Full lower-dimensional induction must still be closed, the complementary regularity range repaired, and global regularity removed through rectangular localization. No compactness, rank-zero image-nullity, or jet-image-nullity premise is supplied separately.

Provenance: byte-identical promotion of `/tmp/SardCriticalImageJetRangeOverlapProbe.lean`, SHA-256 `f889616982056a55e0e42497724179233ac75e75d08fa956fbca9877918bf2b7`. The axiom audit prints only `propext`, `Classical.choice`, and `Quot.sound`.

The stop boundary is failure of rank-zero closedness or exhaustion to transfer compact overlap nullity, failure of the reviewed critical-image assembly under these hypotheses, or a requirement for nonstandard axioms.
