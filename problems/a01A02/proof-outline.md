# Proof Outline: a01A02

## Problem

Let f: ℝⁿ → ℝ be Lebesgue measurable with m{|x : |f(x)| > λ} ≤ Cλ⁻² for some C.
Prove there exists C₁ such that for any Borel set E ⊂ ℝⁿ with 0 < m(E) < ∞,
∫_E |f| dm ≤ C₁ √m(E).

## Harvest Mismatch Note

The informal-solution file `apm-a01A02.md` contains the proof for **a01A01**
(typewriter sequence), not a01A02 (weak-type estimate). The proposed Lean
statements are for the typewriter problem. This bundle implements the correct
problem from `a01A02.tex`.

## Proof Strategy

Layer cake / Cavalieri's principle: ∫_E |f| dm = ∫_0^∞ m(E ∩ {|f| > t}) dt.

Bound: m(E ∩ {|f| > t}) ≤ min(m(E), C/t²).

Split at t₀ = √(C/m(E)):
- ∫_0^{t₀} m(E) dt = √(C·m(E))
- ∫_{t₀}^∞ C/t² dt = √(C·m(E))
- Total = 2√(C·m(E))

So C₁ = 2√C suffices.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 1 (on the main theorem)
- **Classification**: partial
- **Blocker**: layer cake formula application + integral splitting + ENNReal/Real conversions
