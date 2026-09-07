# Nonzero scalar derivative surjectivity

This module turns a nonzero direction for a real-valued continuous linear map
into surjectivity. If `L h ≠ 0`, then the preimage of a scalar `y` is explicitly
`(y / L h) • h`.

The specialized theorem applies this construction to the derivative of a
fixed-direction scalar iterated-jet component. Its hypothesis retains the exact
next-derivative value `ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0`,
and the compiled derivative identity supplies nonvanishing of the derivative
on `h`.

Constructing complemented-kernel or right-inverse data and packaging the
regular level set as an implicit-function hypersurface remain downstream.
