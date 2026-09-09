# Smooth open-domain localization

`exists_smooth_extension_near` constructs g(y)=b(y) • f(y), with a smooth bump centered at x, inner radius epsilon/4 and outer radius epsilon/2 inside a ball contained in the given open U. On U both factors are genuinely smooth. Outside U the bump vanishes on a neighborhood, since its closed support lies inside U; g is therefore smooth there as well. Near x the bump is identically one, so g agrees with f.

`local_image_null_of_global` assumes global genuinely smooth critical-image nullity for the fixed source and target. It constructs these extensions at each critical point of s contained in U, extracts an open neighborhood of equality, and derives fderiv agreement with EventuallyEq.fderiv_eq. Each localized original critical image lies in the actual extension's critical image. Finite dimensionality derives properness and second countability; existing pointwise-open image-null aggregation gives the conclusion for s.

`local_image_null_of_induction` explicitly supplies the global-nullity premise using SardGenuineSmoothGlobalCriticalInductionStep with its existing lower-dimensional induction hypothesis. The target measure remains the original Haar measure.

This result requires ContDiffOn real genuine infinity on an open domain. It does not replace that with pointwise ContDiffAt infinity on an arbitrary set, nor use ContDiffAt.eventually to remove its infinity exclusion. The existing global induction theorem's pointwise-smooth-on-arbitrary-set hypothesis is stronger than this open-domain conclusion. That contract must be repaired or separately discharged before induction closes. Source norm/inner-product transport and actual manifold transport remain outstanding. No unconditional Sard or frozen consumer closure is claimed.
