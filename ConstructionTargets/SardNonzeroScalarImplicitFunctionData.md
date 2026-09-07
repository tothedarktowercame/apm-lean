# Nonzero scalar implicit-function data

This module packages a nonzero strictly differentiable scalar derivative into
Mathlib's exact `ImplicitFunctionData` construction and exposes the resulting
local chart.

For `L h ≠ 0`, the left coordinate is the scalar function with derivative `L`.
The right coordinate is orthogonal projection onto `ker L`. Finite-dimensional
inner-product geometry makes the kernel complete, makes that projection
surjective, and gives complementary derivative kernels. The resulting open
partial homeomorphism sends the basepoint to its scalar value and kernel
coordinate.

The specialized theorem preserves the general target `F`, selected functional
`ℓ`, scalarized function `y ↦ ℓ (iteratedFDeriv ℝ i f y v)`, and exact nonzero
next-jet value with directions `Fin.cons h v`.

The remaining analytic boundary is deriving the required strict derivative of
the scalarized jet from its `ContDiff` regularity before using the chart for
source-dimension reduction.
