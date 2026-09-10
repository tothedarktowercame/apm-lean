# Geometric chart transition units

The module constructs chart-indexed ambient local-homology normalizations over any Type 0 commutative ring R. M is Type 0, Hausdorff and charted on EuclideanSpace ℝ (Fin (m+2)). Each normalization requires x to belong to the actual chart source. No nontriviality, orientation, connectedness, compactness or transition-sign assumption is imposed.

`chartNormalization` uses the full source of chartAt a. `left_restriction` and `right_restriction` identify it with the reviewed common-neighborhood normalization. Consequently `geometric_comparison` identifies N_a inverse followed by N_b with left model normalization inverse, actual overlap transition homology, and right model normalization, in that order.

`linear_scalar` shows that an R-linear endomorphism of R is multiplication by its value at one. `isoUnit` uses the forward and inverse values at one to construct a unit, proving both inverse equations. Applied to the normalization comparison this gives `transitionUnit` and `scalar_action`. The generator-change direction is generator_a = u_ab • generator_b. `geometric_unit` identifies u_ab with the value at one of the actual normalized geometric overlap map. Integer and rational examples are included.

The normalization comparisons satisfy identity, inverse and directed composition equations by cancellation of the intermediate normalization. Their units satisfy u_ab*u_bc=u_ac, u_aa=1 and inverse(u_ab)=u_ba. These are proved normalization-comparison cocycles. Explicit point-set and pair-map composition on a common triple overlap remains a separate geometric obligation.

The Lean source exactly matches fixture SHA256 e3f94ec9e7e0dcd4438b5c84ff78bc1cce3bbc08b0c152b511fda16326f06d36 and contains fifteen standard-only axiom audits. The separately reserved distinguished-chart recovery is untouched. Recovery of CoefficientChartLocal.localIso, explicit triple-overlap composition, local constancy, orientation compatibility and global localization remain downstream; no consumer closure is claimed.
