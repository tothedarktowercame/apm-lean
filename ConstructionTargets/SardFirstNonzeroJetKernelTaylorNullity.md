# First nonzero jet kernel Taylor nullity

`firstNonzeroJet_kernelChart_image_null_of_taylor_surplus` proves zero
target add-Haar measure of the image of a first-nonzero-(i+1)-jet locus
intersected with an implicit-function chart source. Here i is positive,
the chart left coordinate is a fixed-direction scalarized i-jet, and its
base point lies in the same first-nonzero-jet locus. The ambient map is
globally C^(i+1). The exact inverse kernel parametrization is assumed C1
at every point of the chart's constant-left-coordinate target slice.

The strict bound is `kernelDim < (i+1)*targetDim`. The kernel and target
spaces are nontrivial finite-dimensional real inner-product spaces with
Borel structures; the kernel space is proper and second countable. The
ambient space is a proper real normed space. No lower-dimensional Sard
nullity hypothesis or automatic remaining-order admissibility is assumed.

The observed dependencies are `SardFirstNonzeroJetKernelParameterContainment`
and `SardC1ParameterizedFlatLocusNullity`. The target slice is open by
continuity of insertion of the fixed left coordinate. Kernel containment
supplies a parameter witness for each localized jet point. Equality of
its parameter image with that point transfers vanishing of derivatives
through order i into the exact flat parameter locus. Image containment
and measure monotonicity then transfer the banked parameter nullity to
the localized jet image. The chart-source intersection is retained.

The intended consumer is t93A04; additional proposed consumers are t01A08,
t01J04, t92J07, and t96J05. Supplying C1 kernel-chart regularity through
chart refinement and aggregating applicable local images remain. Jet
cases outside the strict dimension range still require analytic repair
before rectangular induction. No frozen consumer is changed or closed.

The source is byte-identical to the accepted fixture
`/tmp/SardFirstNonzeroJetKernelTaylorNullityProbe.lean`, SHA-256
`ed5766a7b38622e04a88e4aaf0ef1791664629c98377d0769560dd36809d2495`.
The declaration uses only propext, Classical.choice, and Quot.sound.
The stop boundary is failure of the stated kernel containment and flat
parameter nullity to imply localized image nullity, or a need for
nonstandard axioms.
