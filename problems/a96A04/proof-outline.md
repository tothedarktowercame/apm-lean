# Proof Outline: a96A04

## Problem

u(x,t) = (4πt)^{-n/2} ∫ e^{-|x-y|²/(4t)} f(y) dy.
(a) u smooth in x for t > 0.
(b) ‖u‖₂ ≤ ‖f‖₂.
(c) u → f in L² as t → 0⁺.

## Formalization (1D for clean compilation)

Used ℝ (1D) instead of ℝⁿ to avoid EuclideanSpace measure setup.
Definitions: heatKernel, heatConv (Bochner integral).

## Theory boundaries (4 sorries)

1. `heatKernel_integral`: ∫G_t = 1 (Gaussian integral).
2. `heatConv_contDiff` (part a): DCT for differentiation under integral.
3. `heatConv_L2_le` (part b): Young's inequality (NOT in Mathlib).
4. `heatConv_tendsto_L2` (part c): approximate identity / Fourier + DCT.

## Checked Lean state

- `lake env lean problems/a96A04/lean/Main.lean`: exit 0
- Sorry count: 4
- Classification: partial
