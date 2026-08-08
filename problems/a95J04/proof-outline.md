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

## Remaining bridge (1 sorry)

1. If there is no boundary pole, obtain a uniform disk of radius greater than
   one on which `f` is holomorphic, identify `a` with its Taylor coefficients,
   and contradict `hradius_gt`.
2. Under the simple-pole hypothesis, subtract the now-finite collection of
   principal parts, extend the remainder holomorphically, and
   compare Taylor coefficients to obtain a uniform bound.

## Checked Lean state

- `lake env lean problems/a95J04/lean/Main.lean`: exit 0
- Sorry count: 1
- Classification: partial
