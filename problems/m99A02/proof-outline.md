# Proof Outline: m99A02

Compiled preliminaries establish positivity of the logarithmic base and of the
chosen representative on the punctured disk.  Closer hop 1 also proves global
measurability of the function and both displayed derivatives, including the
singleton split at the origin.

Closer hop 2 proves the exact pointwise radial identity
`sum i, (m99A02Derivative i x)^2 =
1 / (9 * ‖x‖^2 * (-log ‖x‖)^(4/3))` away from the origin. This closes the
coordinate algebra using `EuclideanSpace.real_norm_sq_eq` and reduces both
derivative `L²` bounds to the single scalar Bertrand density.

Closer hop 3 proves the coordinatewise consequence
`(m99A02Derivative i x)^2 ≤
1 / (9 * ‖x‖^2 * (-log ‖x‖)^(4/3))` with `Finset.single_le_sum`.
Thus one radial integrability result now suffices uniformly for both derivative
coordinates.

Sibling `a01A07` provides a proved polar-coordinate formula on `ℂ`.  The next
step is transporting the `EuclideanSpace ℝ (Fin 2)` disk and volume to `ℂ`, then
proving the radial logarithmic integrability bounds.  The weak derivative still
requires punctured-disk integration by parts and vanishing boundary flux.
