# Sphere-cap graph densities

This module simplifies the norms and L2 graph densities of the reviewed upper
and lower sphere-cap height derivatives on the open unit ball.

The upper derivative is first rewritten as the inner-product functional at
`x`, scaled by `-1 / upper x`. The norm calculation uses the exact norm of
`innerSL ℝ x` and strict positivity of the upper height. Negation gives the
same norm for the lower derivative:

`‖upperDerivative x‖ = ‖lowerDerivative x‖ = ‖x‖ / upper x`.

Substituting the reviewed identity `upper x ^ 2 = 1 - ‖x‖ ^ 2` into the
literal L2 graph-density square gives `1 / upper x ^ 2` for both derivatives.
Nonnegativity and strict positivity select the positive square root, so both
actual graph densities equal `1 / upper x`. The final lemmas transfer these
formulas to the actual `fderiv`s. Dimension-two and dimension-three examples
compile for both signs, and all eight requested audits use only standard
axioms.

The remaining work constructs the explicit `WithLp 2` coordinate isometry,
identifies the graph images and subtypes with the strict sphere caps, and
transports the reviewed exact graph-area equation. This module contains no
isometry, measure transport, normalization, equator, moment, or
consumer-closure claim.
