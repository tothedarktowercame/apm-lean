# Smooth implicit charts from neighborhood data

Probe: sard-smooth-neighborhood-implicit-chart-probe-refill10.
Candidate production module: ConstructionTargets/SardSmoothNeighborhoodImplicitChart.lean.

`exists_smooth_neighborhood_restriction` takes an actual open partial
homeomorphism, an open U inside its source containing the basepoint, genuine
C-infinity smoothness on U, and an invertible derivative at the basepoint.
Continuity of the first derivative and openness of the continuous-linear-
equivalence locus supply a smaller open V. Restricting the original chart to V
preserves its forward function and inverse function. The restricted source is
contained in U, contains the original basepoint, and has invertible derivative
at every point. The existing inverse regularity theorem then supplies
C-infinity on the restricted target.

`exists_smooth_implicit_chart` instantiates this result with the literal chart
from ImplicitFunctionData and the derivative equivalence supplied by its
surjective complementary derivative pair. The only additional regularity
assumptions are ContDiffOn at genuine infinity for leftFun and rightFun on U.
It returns the source inclusions, original prodFun, inverse agreement on the
new target, and smoothness in both directions. No analytic outer-top premise
or nullity premise is used. The proof works for the stated complete normed
spaces without needing finite-dimensional assumptions, hence covers the
requested finite-dimensional spaces.

`exists_smooth_chart_with_residual_slices` is the exercised consumer: it takes
an additional smooth f on the SAME U and continuous linear Q, obtains the new
chart from the preceding producer, restricts f's regularity to its source,
and invokes SardProjectedChartResidualSlicesContDiffOn at infinity. Thus the
output inverse smoothness is actually consumed by the existing slice theorem.

This is distinct from SardImplicitFunctionDataSmoothChart's pointwise theorem,
which excludes infinity. Its pointwise ContDiffAt premise is not sufficient for
a common smooth neighborhood. No exclusion is removed, no linter disabled,
and the existing theorem is unchanged.

The new result does not construct smooth-on-neighborhood scalarized jet data,
replace the arbitrary-C1 induction quantifier, prove local critical nullity,
handle the full induction base cases, or close manifold Sard. Frozen t93A04
retains its one placeholder. The implementation packet should promote this
fixture and explanation only, with independent compilation and axiom review.
