# Proof Outline: a94A03

## Problem

For f in Lp(R), 1 <= p < infinity, t > 0: K_t(f)(x) = (1/t) integral e^{-pi(x-y)^2/t^2} f(y) dy.
(a) K_t maps unit ball of Lp into itself.
(b) K_t f -> f in Lp as t -> 0.

## Proven zero-sorry

- `gaussKernel_nonneg`: kernel is nonneg

## Remaining sorries (3)

1. `gaussKernel_integral_eq_one`: kernel integrates to 1 (Gaussian integral)
2. `gaussConv_Lp_contraction` (part a): Young's convolution inequality (not in Mathlib)
3. `gaussConv_tendsto_Lp` (part b): Lp convergence (needs translation continuity + Minkowski)

## Lean state

- **Checked:** exit 0, 0 errors, 3 sorries
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a94A03/lean/Main.lean`

## References

- Key Mathlib: `convolution`, `gaussian_integral`, `eLpNorm`, `MemLp`
- Missing: Young's convolution inequality, Lp translation continuity
