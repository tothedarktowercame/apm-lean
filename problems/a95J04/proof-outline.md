# Proof Outline: a95J04

## Problem

f analytic on Δ, power series radius = 1, extends meromorphically to D ⊃ Δ̄.
(a) f has at least one pole on ∂Δ.
(b) Simple boundary poles ⟹ bounded coefficients.

## Compiled reduction

- `apm_a95J04_pole_mem_sphere_of_mem_closedBall`: any pole in the closed
  unit disk lies on its boundary. Analyticity in the open disk gives
  `0 ≤ meromorphicOrderAt f z`, contradicting negative order there.
- `apm_a95J04_boundary_poles_finite`: restrict the meromorphic divisor to
  the compact unit sphere; its locally finite support becomes finite, and
  every negative-order boundary point belongs to that support.

## Stated bridges (5 sorries total)

Hop 4 intentionally states, without proving, four exact missing lemmas:

1. `apm_a95J04_bridge_taylor_coefficients` identifies `a n` with the
   normalized iterated derivative at zero.
2. `apm_a95J04_bridge_absolute_convergence` gives absolute convergence at
   every nonnegative radius strictly inside a holomorphic disk.
3. `apm_a95J04_bridge_holomorphic_past_circle` produces a uniformly larger
   disk when there are no boundary poles.
4. `apm_a95J04_bridge_simple_pole_decomposition` subtracts the finite set of
   simple boundary principal parts and leaves a function holomorphic on a
   uniformly larger disk.

Together these reduce the main theorem to finite-sum coefficient algebra and
direct applications of the stated bridges.

## Checked Lean state

- `lake env lean problems/a95J04/lean/Main.lean`: exit 0
- Sorry count: 5 (four requested bridge declarations plus the main theorem)
- Classification: partial
