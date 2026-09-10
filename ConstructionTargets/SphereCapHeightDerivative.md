# Sphere-cap height derivatives

This module computes the exact Fréchet derivatives of the reviewed upper and
lower sphere-cap height functions on the open unit ball in
`EuclideanSpace ℝ (Fin d)`.

`upperDerivative d x` is the derivative of square root applied to one minus
the norm square: the negative norm-square derivative is scaled by
`1 / (2 * upper d x)`. Strict positivity of the reviewed radicand justifies
the square-root differentiation. `lowerDerivative d x` is its negative.

The `HasFDerivAt` and `fderiv` equalities identify these constructed maps with
the actual derivatives of both height functions. The application lemmas expand
the maps into explicit real inner-product formulas. Dimension-two and
dimension-three examples compile for both signs, and all ten requested audits
use only standard axioms.

The remaining work computes the norms of these derivative maps and simplifies
the graph densities, constructs the explicit `WithLp 2` coordinate isometry,
identifies the graph images with the strict sphere caps, and transports the
reviewed exact graph-area equation. This module contains no density, isometry,
measure, normalization, equator, moment, or consumer-closure claim.
