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

## Remaining sorries (4)

1. `unifIntegrable_of_L2_bounded`: UI of {fₙ} in Lp from L² bound (Hölder)
2. `hg2`: MemLp g 2 μ (Fatou's lemma)
3. `hgp`: MemLp g p μ (L²→Lp embedding on finite measure)
4. `hui_sub`: UI of {fₙ-g} from UI of {fₙ}

## Lean state

- **Checked:** exit 0, 0 errors, 4 sorries
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a93A02/lean/Main.lean`

## References

- Key Mathlib: `tendsto_Lp_finite_of_tendsto_ae`, `UnifIntegrable`,
  `MemLp`, `eLpNorm`
