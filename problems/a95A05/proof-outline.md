# Proof Outline: a95A05

## Problem

If f is analytic on the open disk Δ, continuous on Δ̄, and vanishes on the
upper semicircle of ∂Δ, prove f ≡ 0 on Δ.

## Proof strategy

1. Define g(z) = f(z)·f(-z). ✓ All properties proved:
   - `auxProd_differentiableOn`: g is analytic on Δ.
   - `auxProd_continuousOn`: g is continuous on Δ̄.
   - `auxProd_vanish_on_frontier`: g = 0 on all of ∂Δ.
   - `eq_zero_on_closure_of_frontier_zero`: maximum modulus principle gives g ≡ 0 on Δ̄.

2. From f(z)·f(-z) = 0 for all z ∈ Δ, conclude f ≡ 0. ✗ SORRY.
   Requires the identity theorem: zeros of a nonzero analytic function on a
   connected domain form a discrete set. Since f·(f∘(-id)) ≡ 0, one factor
   must vanish identically.

## Proved lemmas (zero sorry)

- `auxProd_differentiableOn`: f(z)·f(-z) is analytic on the disk.
- `auxProd_continuousOn`: f(z)·f(-z) is continuous on the closed disk.
- `auxProd_diffContOnCl`: combining the above into DiffContOnCl.
- `auxProd_vanish_on_frontier`: g vanishes on the entire unit circle
  (case split on Im z ≥ 0 vs < 0, using f(-z) = 0 when Im z < 0).
- `ball_bounded`: the open unit disk is bounded.
- `eq_zero_on_closure_of_frontier_zero`: maximum modulus principle via
  Mathlib's `Complex.eqOn_closure_of_eqOn_frontier`.

## Checked Lean state

- `lake env lean problems/a95A05/lean/Main.lean`: exit 0
- Sorry count: 1
- Classification: partial
