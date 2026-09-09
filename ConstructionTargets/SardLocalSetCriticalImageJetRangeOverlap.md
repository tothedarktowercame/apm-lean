# Local-set critical-image nullity under jet-range overlap

The declaration `localSet_criticalImage_zero_of_jet_range_overlap_induction` proves zero target add-Haar measure of the nonsurjective-derivative image restricted to an arbitrary source subset s.

Regularity is ambient `ContDiffAt` of finite order k+2 at every member of s, not merely `ContDiffWithinAt`. The source set need not be open or measurable. Classical admissibility, full classical critical-image nullity at every strictly lower source dimension, and the overlap bound
`sourceDim + (sourceDim - 1) / targetDim <= targetDim + k + 3`
remain hypotheses. Division is natural-number division. The statement also retains nontrivial finite-dimensional real inner-product spaces, Borel structures, a proper source, and a target add-Haar measure.

At a critical point in s, finite-order ambient regularity persists on a neighborhood. An open refinement gives the regularity required by the reviewed open-source overlap theorem. The image of the critical source set intersected with that neighborhood is contained in its open critical image. Measure monotonicity gives local nullity, and second-countable aggregation gives the result on s. Finiteness of the order is explicitly justified by `ENat.natCast_ne_coe_top`.

The direct import is `SardOpenCriticalImageJetRangeOverlap`. The proof uses its `open_criticalImage_zero_of_jet_range_overlap_induction` and the transitively imported `SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null`. These are observed dependency uses. The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers, not claimed uptake.

Open-source and global-regularity restrictions are discharged in the conditional overlap regime. Full lower-dimensional induction and the complementary regularity range remain unresolved. Only after those obligations are closed can an unrestricted local-set theorem be connected to manifold chart assembly; this module does not close general rectangular Morse–Sard.

Provenance: byte-identical promotion of `/tmp/SardLocalSetCriticalImageJetRangeOverlapProbe.lean`, SHA-256 `7e59e1db58f0c1a0b9dc2dc937c3d1119222d7b11f54ce7d4374be9ef8cd3ed0`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if finite-order ambient regularity fails to supply the required open neighborhoods, restriction and countable aggregation fail under the stated hypotheses, or nonstandard axioms are required.
