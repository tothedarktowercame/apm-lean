# Proof Outline: m98J05

Closer hop 1 proves the Fourier differentiation clause completely.  The custom
kernel `exp (-i ξ x)` is Mathlib's `2π`-scaled Fourier transform evaluated at
`ξ/(2π)`.  Applying `Real.fourier_deriv` at that frequency and cancelling the
scale gives `F(f') = iξ F(f)`.

The custom Fourier integrand's absolute integrability and the scalar multiplier
ODE are also compiled.  Remaining work is the heat-kernel transform and
convolution identity, differentiation under spatial/time integrals, and
pointwise approximate-identity convergence for complex `L¹` data.
