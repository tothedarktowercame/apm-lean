# Scalarized-jet exact implicit-function data

This module exposes the exact `ImplicitFunctionData` underlying the local
hypersurface chart for a selected scalarized fixed-direction jet.

For a scalar strict derivative nonzero on one direction, it constructs the
kernel's finite-dimensional complete-space witness and packages the scalar
function, its derivative, and orthogonal kernel projection into Mathlib's
exact implicit-function data. The specialized theorem derives the strict
derivative from `ContDiff ℝ (i + 1)` and retains the general target, selected
functional, `iteratedFDeriv`, and `Fin.cons` representations.

The result exposes the original scalarized function and derivative fields and
certifies that the base point belongs to the chart source. Applying the
level-set coordinate identity and transporting localized nonzero-jet strata
to the lower-dimensional kernel remain downstream.
