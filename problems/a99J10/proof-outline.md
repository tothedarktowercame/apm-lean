# Proof Outline: a99J10

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves:

- the exact imaginary-part formula for the polar parametrization;
- membership of `r exp(iθ)` in the unit disk for `0 ≤ r < 1`;
- the explicit bound `‖f (r exp(iθ))‖ ≤ |r sin θ|⁻¹ᐟ²` away from the
  real-axis angles.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a99J10.md`

## Remaining boundary

- prove interval integrability of `θ ↦ |sin θ|⁻¹ᐟ²`, handling its endpoint
  singularities by comparison with inverse square roots;
- apply dominated convergence to the circle/Cauchy integrals using the radial
  limits;
- identify the limiting Cauchy integral with each interior value and conclude
  that value is zero.

Mathlib's Phragmén–Lindelöf file was inspected, but its packaged strip/sector
theorems require continuous boundary bounds rather than these radial limits.
