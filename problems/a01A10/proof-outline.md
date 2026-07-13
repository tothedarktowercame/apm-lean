# Proof Outline: a01A10

## Problem

Use a contour integral to compute one of:
(a) ∫₀^∞ e^{ix²} dx
(b) ∫_{-∞}^∞ e^{ixy} e^{-x²} dx

## Harvest Mismatch Note

The informal-solution file `apm-a01A10.md` contains the proof for **a01A09**
(Laplace transform analyticity), not a01A10 (contour integral). This bundle
implements the correct problem from `a01A10.tex`.

## Answers

- Part (b): ∫ e^{ixy} e^{-x²} dx = √π · e^{-y²/4}
- Part (a): ∫₀^∞ e^{ix²} dx = (1+i)√π/(2√2)

## Proof Strategy

(b): Complete the square: -x²+ixy = -(x-iy/2)² - y²/4. Contour shift gives
∫ e^{-(x-iy/2)²} dx = ∫ e^{-x²} dx = √π (Mathlib: `integral_gaussian`).

(a): Contour over sector {re^{iθ}: 0 ≤ θ ≤ π/4}, Cauchy's theorem, convert
oscillatory integral to convergent one.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 3 (main theorems + complete_square helper)
- **Classification**: partial
