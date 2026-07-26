# Proof Outline: a95J04

## Problem

f analytic on Δ, power series radius = 1, extends meromorphically to D ⊃ Δ̄.
(a) f has at least one pole on ∂Δ.
(b) Simple boundary poles ⟹ bounded coefficients.

## Proved lemmas

- `isCompact_unit_sphere`: ∂Δ is compact.
- `coefficients_bounded_simple_pole`: Taylor coefficients of c/(z-ζ),
  |ζ|=1, are bounded by |c|. Key: |ζ^n| = 1.

## Theory boundaries (3 sorries)

1. `holo_on_larger_ball_implies_bounded`: bounded image of compact (API).
2. `exists_pole_on_boundary` (part a): meromorphic theory + radius of convergence.
3. `coefficients_bounded_of_simple_poles` (part b): pole subtraction + Cauchy.

## Checked Lean state

- `lake env lean problems/a95J04/lean/Main.lean`: exit 0
- Sorry count: 3
- Classification: partial
