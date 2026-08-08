# Proof Outline: a93A02

## Problem

{fₙ} ⊂ L²([0,1]), sup ‖fₙ‖₂ < ∞, fₙ → f a.e., 1 ≤ p < 2.
Prove ‖fₙ - f‖ₚ → 0.

## Proof

By Vitali's convergence theorem (`tendsto_Lp_finite_of_tendsto_ae`):
a.e. convergence + uniform integrability ⟹ Lp convergence.

## Proven zero-sorry

- **Vitali application**: `tendsto_Lp_finite_of_tendsto_ae` applied to
  hₙ = fₙ - g → 0 a.e. with hₙ uniformly integrable.
- a.e. convergence of fₙ - g to 0 (from Tendsto.sub + const).
- p ≠ ∞ from p < 2.

## Closer hop 1

The complete positive result is compiled. The earlier proof at commit
`4f07f5f` was localized: exponent comparison gives uniform integrability,
Fatou gives the `L²` bound for the a.e. limit, and Mathlib's finite-measure
Vitali theorem gives `Lᵖ` convergence.

The sole remaining hole is the explicit counterexample conjunction. It needs
the calculation that the spike `sqrt(n+1) 1_[0,1/(n+1)]` has `L²` norm one,
eventual pointwise vanishing away from the null singleton `{0}`, and the
resulting failure of norm convergence.

## Lean state

- **Checked:** exit 0, 0 errors, 1 sorry
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a93A02/lean/Main.lean`

## References

- Key Mathlib: `tendsto_Lp_finite_of_tendsto_ae`, `UnifIntegrable`,
  `MemLp`, `eLpNorm`
