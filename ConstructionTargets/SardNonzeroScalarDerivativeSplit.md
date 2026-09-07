# Nonzero scalar derivative splitting

This module constructs split data from a direction on which a scalar continuous
linear map is nonzero.

For `L h ≠ 0`, the right inverse sends `y` to `(L h)⁻¹ y • h`. The construction
is continuous linear and satisfies `L (R y) = y`. Mathlib's
`ContinuousLinearMap.projKerOfRightInverse` then gives the canonical continuous
linear projection from the source into `ker L`.

The specialized theorem retains the general target `F`, the selected functional
`ℓ : F →L[ℝ] ℝ`, and the scalarized function
`y ↦ ℓ (iteratedFDeriv ℝ i f y v)`. Its exact next-jet hypothesis is
`ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0`.

Exact `ImplicitFunctionData` packaging and the resulting local hypersurface and
source-dimension reduction remain downstream.
