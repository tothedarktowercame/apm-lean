# Small-source critical-image induction

`smallSource_local_criticalImage_zero_of_lowerDimension_induction` proves zero target add-Haar measure for the image of the nonsurjective-derivative locus restricted to an arbitrary source subset.

The hypotheses retain global C^(k+1) regularity, classical Sard order admissibility, source dimension at most twice target dimension, and classical critical-image nullity at every strictly lower source dimension. The source and target have the nontrivial finite-dimensional real inner-product and Borel structures stated in the Lean declaration; the source is proper.

The proof supplies the reviewed small-source rank-zero nullity theorem to the finite-order critical-image assembly, then restricts the resulting null image by measure monotonicity. No additional rank-zero nullity premise is required.

This is a conditional induction step, not a closed rectangular Morse–Sard theorem. The full lower-dimensional classical nullity hypothesis still needs a valid induction, including larger-source regimes: the small-source dimension bound alone does not close that induction. Removing global regularity through rectangular localization also remains. The frozen t93A04 consumer is unchanged.

The Lean source is promoted byte-for-byte from `/tmp/SardSmallSourceCriticalImageInductionProbe.lean`, SHA-256 `b4bda6a57b8d4244df2d63c8cf5f520f6b5db93de6a125880e18a44d65e76b74`. Its axiom audit is included with `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` are expected.
