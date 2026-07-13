# Proof Outline: a01A04

## Problem

Let B_{m,1} denote the unit ball in ℝᵐ. Three parts:
(a) Show ∃ f: ℝ → [0,1] such that m(B_{n+1,1}) = m(B_{n,1}) · ∫ [f(t)]ⁿ dt.
(b) Show ∫ [f(t)]ⁿ dt → 0 as n → ∞.
(c) Show for any finite positive A, Aⁿ · m(B_{n,1}) → 0 as n → ∞.

## Harvest Mismatch Note

The informal-solution file `apm-a01A04.md` contains the proof for **a01A03**
(convolution identity), not a01A04 (unit ball volumes). The proposed Lean
statements are for the convolution problem. This bundle implements the correct
problem from `a01A04.tex`.

## Proof Strategy

(a) Slice B_{n+1,1} ⊂ ℝⁿ × ℝ along last coordinate. For each t, the slice is
    B_{n,√(1-t²)} with volume (√(1-t²))ⁿ · m(B_{n,1}). So f(t) = √(1-t²).
(b) Dominated convergence: f(t)ⁿ → 0 for t ≠ 0, |f(t)ⁿ| ≤ 1.
(c) m(B_{n,1}) = m(B_{1,1}) · ∏ ∫fᵏ, each factor → 0, so product → 0.

## Proved Lemmas

- `ballSlice_nonneg`: f(t) ≥ 0
- `ballSlice_le_one`: f(t) ≤ 1

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 3 (parts a, b, c)
- **Proved lemmas**: `ballSlice_nonneg`, `ballSlice_le_one`
- **Classification**: partial
