# Proof Outline: a95J08

## Problem

f ∈ L¹(ℝ), g ∈ Lp(ℝ), 1 < p < ∞.
(a) y ↦ f(x-y)g(y) is integrable for a.e. x.
(b) ‖f*g‖_p ≤ ‖f‖₁ · ‖g‖_p (Young's inequality).

## Theory boundaries (4 sorries)

1. `integral_translate_norm`: ∫|f(x-y)|dx = ∫|f(x)|dx (needs measurePreserving_sub_left composition).
2. `convolution_integrand_integrableAE` (part a): Hölder + Tonelli argument.
3. `young_convolution_inequality` (part b): Young's inequality NOT in Mathlib.
4. `convolution_memLp`: inherits from above.

## Checked Lean state

- `lake env lean problems/a95J08/lean/Main.lean`: exit 0
- Sorry count: 4
- Classification: partial
