# First-nonzero-jet scalarized chart data

This module packages the analytic data needed to turn a nonzero successor jet into a lower-dimensional implicit chart.

From a nonzero derivative of order `i + 1`, it selects a first direction, tail directions, and a continuous linear scalar functional with nonzero scalar evaluation. It then constructs exact scalarized `ImplicitFunctionData`, retains the defining left function, derivative, and base point, proves smoothness of the inverse-chart kernel parameter at the base coordinate, and records the strict kernel finrank decrease.

The package is the direct input for promoting base-point kernel regularity to an open neighborhood and constructing pointwise local-nullity witnesses on refined first-nonzero-jet loci.
