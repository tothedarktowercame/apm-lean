# Proof Outline: a99J10

The canonical Lean attempt is `lean/Main.lean`. Closer hops 1–2 prove:

- the exact imaginary-part formula for the polar parametrization;
- membership of `r exp(iθ)` in the unit disk for `0 ≤ r < 1`;
- the explicit bound `‖f (r exp(iθ))‖ ≤ |r sin θ|⁻¹ᐟ²` away from the
  real-axis angles;
- integrability of the model inverse-square-root kernel on `(0, pi/2)`;
- Jordan-inequality domination of the sine singularity by that model kernel
  on the first quadrant.
- a uniform estimate for all `1/2 ≤ r < 1`, bounding the radial values by
  `(1/2)⁻¹ᐟ² * |sin θ|⁻¹ᐟ²` independently of `r`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a99J10.md`

## Remaining boundary

- prove interval integrability of `θ ↦ |sin θ|⁻¹ᐟ²`, handling its endpoint
  singularities on the other quadrants by symmetry and assemble the pieces;
- apply dominated convergence to the circle/Cauchy integrals using the radial
  limits;
- identify the limiting Cauchy integral with each interior value and conclude
  that value is zero.

Mathlib's Phragmén–Lindelöf file was inspected, but its packaged strip/sector
theorems require continuous boundary bounds rather than these radial limits.
