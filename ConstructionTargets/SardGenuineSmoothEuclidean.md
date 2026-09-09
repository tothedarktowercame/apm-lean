# Unconditional genuine-smooth Euclidean Sard

`SardGenuineSmoothEuclideanProbe.critical_image_null` proves that the actual
nonsurjective-fderiv critical set of a globally ContDiff real infinity map
has Haar-null image. Its source is any finite-dimensional complete real
inner-product space; its target is any finite-dimensional real inner-product
space with Borel Haar measure. There is no nullity or induction premise.
Source and target universes are quantified independently.

`critical_image_null_of_smaller_global` is the induction step. A subsingleton
target has empty critical set because every derivative is surjective. A
subsingleton source is handled by the existing zero-dimensional critical-image
theorem. Otherwise source Borel structure and properness are derived locally.
Smoothness gives closedness of the derivative-rank-zero locus. Existing
closed/open image-null assembly constructs its countable compact exhaustion;
rank zero implies the derivative is zero on each compact. The repaired
compact rank-zero theorem applies smaller-dimensional global induction through
its open-domain localization compatibility. The repaired positive-rank
stratum theorem supplies every positive deficient rank. Existing critical-rank
coverage and countable-null assembly combine these into the full critical set.

`critical_image_null_by_dimension` discharges the premise by strong induction
on source finrank, quantifying every source, target and Haar measure at each
dimension. Smaller kernel sources remain in the same source universe, and
complementary targets in the same target universe. Dimension zero is included.

`open_domain_critical_image_null` invokes the existing cutoff localization
with the unconditional global theorem. For ContDiffOn real infinity f on
an explicitly open U and any subset s of U, it proves nullity of the image
of s intersected with the actual nonsurjective-fderiv locus. No measurability
of s and no arbitrary-set pointwise infinity assumption is required.

All four declarations print only propext, Classical.choice and Quot.sound.
Existing APIs and frozen consumers remain unchanged. This proves Euclidean
inner-product-space genuine-smooth Sard, not a manifold theorem or frozen
t93A04 closure. Any required normed-source comparison and actual manifold
chart, criticality and measure transports remain downstream.
