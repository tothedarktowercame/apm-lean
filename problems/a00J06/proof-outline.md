# Proof Outline: a00J06

## Problem

Let f(z) = Σ a(n)zⁿ have radius of convergence 1, with 0 ≤ a(n) for all n.
Prove that z=1 is a singular point: f cannot be analytically continued onto
a disk centered at z=1 with positive radius.

## Harvest Mismatch Note

The informal-solution file `apm-a00J06.md` was harvested with the **wrong
content**: it contains the proof for a00J05 (Cauchy transform of compact set),
not a00J06 (singularity of power series with nonneg coefficients). The Lean
statements in that file are for the Cauchy transform problem. This bundle
implements the correct problem from `a00J06.tex`.

## Proof Strategy

Contradiction argument. If f extends analytically to B(1, ρ) with ρ > 0:
1. Pick x ∈ (1-ρ, 1). Taylor series of f at x has radius > 1-x.
2. Taylor coefficients at x: b(n) = Σ_{k≥n} C(k,n) a(k) x^{k-n} ≥ 0.
3. Evaluating at 1-x+ε: Σ b(n)(1-x+ε)ⁿ = Σ_k a(k)(1+ε)^k < ∞ (Tonelli).
4. But Σ a(k)(1+ε)^k < ∞ implies radius > 1 (proved in radius_gt_one_of_summable).
5. Contradiction with radius = 1.

## Proved Lemma

**`radius_gt_one_of_summable`** (sorry-free): If Σ a(n)(1+ε)^n converges
for ε > 0, then the radius of convergence of Σ a(n)zⁿ exceeds 1. This uses
`FormalMultilinearSeries.le_radius_of_summable` and the norm computation
`‖ofScalars ℝ a n‖ = |a(n)| = a(n)` (by NormOneClass and a(n) ≥ 0).

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 1 (on the main theorem `singular_at_one`)
- **Proved lemma**: `radius_gt_one_of_summable`
- **Classification**: partial

## Statement Repair

The proposed Lean statements from the informal proof file are for the wrong
problem (a00J05, Cauchy transform). This file implements the correct problem
(a00J06, singularity at z=1 of power series with nonneg coefficients) using
`FormalMultilinearSeries.ofScalars` for the power series representation.
