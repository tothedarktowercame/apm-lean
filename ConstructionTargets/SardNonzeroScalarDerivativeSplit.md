# Nonzero scalar derivative splitting

This module constructs split data from a direction on which a scalar continuous
linear map is nonzero.

For `L h ≠ 0`, the right inverse sends `y` to `(L h)⁻¹ y • h`. The construction
is continuous linear and satisfies `L (R y) = y`. Mathlib's
`ContinuousLinearMap.projKerOfRightInverse` then gives the canonical continuous
linear projection from the source into `ker L`.

The specialized theorem applies the construction to the derivative of a scalar
fixed-direction iterated jet. It retains the exact next-jet hypothesis with
directions ordered as `Fin.cons h v`.

Exact `ImplicitFunctionData` packaging and the resulting local hypersurface and
source-dimension reduction remain downstream.
