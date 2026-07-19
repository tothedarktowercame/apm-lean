import Mathlib.Analysis.Complex.Liouville

/-!
# APM a94J08: No entire function satisfies |f(z)| ≥ |z|^{3/2}

## Problem (from `a94J08.tex`)

Prove that no entire function `f` can satisfy `|f(z)| ≥ |z|^{3/2}` for all
complex numbers `z`.

## Proof strategy

Suppose `f` is entire with `|f(z)| ≥ |z|^{3/2}` for all `z`.

**Case A: `f(0) ≠ 0`.** Then `f` never vanishes (for `z ≠ 0`, `|f(z)| ≥ |z|^{3/2} > 0`).
So `g = 1/f` is entire. For `|z| ≥ 1`: `|g(z)| = 1/|f(z)| ≤ 1/|z|^{3/2} ≤ 1`.
For `|z| ≤ 1`: `g` is continuous on the compact set `closedBall 0 1`, hence bounded.
So `g` is bounded everywhere. By Liouville, `g` is constant, so `f` is constant.
But `|f(z)| ≥ |z|^{3/2}` is impossible for a constant and large `|z|`. Contradiction.

**Case B: `f(0) = 0`.** Then `f(z) = zⁿ h(z)` with `h` entire, `h(0) ≠ 0`, `n ≥ 1`.
The bound gives `|h(z)| ≥ |z|^{3/2 - n}` for `z ≠ 0`.
- If `n ≥ 2`: `|h(z)| ≥ |z|^{-1/2} → ∞` as `z → 0`, contradicting `h` continuous at `0`.
- If `n = 1`: `h` is entire, `h(0) ≠ 0`, `|h(z)| ≥ |z|^{1/2}`. Apply Case A to `h`.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Bornology Set Metric

open scoped Real

namespace ApmCanaries.A94J08

/-- Helper: `a⁻¹ ≤ 1` when `1 ≤ a`. -/
lemma inv_le_one_of_le_one {a : ℝ} (ha : 1 ≤ a) : a⁻¹ ≤ 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have : a⁻¹ = 1 / a := by rw [one_div]
  rw [this]; exact (div_le_one ha0).mpr ha

/-- Helper: `f(z) ≠ 0` for `z ≠ 0` from the lower bound. -/
lemma nonzero_of_lower_bound
    (f : ℂ → ℂ)
    (hbound : ∀ z, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖)
    (z : ℂ) (hz : z ≠ 0) : f z ≠ 0 := by
  intro h
  have hb := hbound z
  rw [h] at hb; simp at hb
  linarith [Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) ((3:ℝ)/2)]

/-- Helper: `‖1/f(z)‖ ≤ 1` for `|z| ≥ 1`. -/
lemma norm_inv_le_one_of_lower_bound
    (f : ℂ → ℂ) (hf_ne : ∀ z, f z ≠ 0)
    (hbound : ∀ z, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖(f z)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact inv_le_one_of_le_one
    ((Real.one_le_rpow hz (by norm_num)).trans (hbound z))

/-- **Main theorem.** No entire function satisfies `|f(z)| ≥ |z|^{3/2}`.

    The proof splits into cases on whether `f(0) = 0`.

    **SORRY BOUNDARY:** The boundedness of `1/f` on the compact disk
    `closedBall 0 1` requires combining the local bound with the global bound
    via compactness arguments. The Case B factorization `f(z) = zⁿ h(z)` requires
    Mathlib's analytic order theory (`analyticOrderAt`). -/
theorem no_entire_lower_bound_three_halves :
    ¬∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ z : ℂ, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖ := by
  rintro ⟨f, hf_diff, hbound⟩
  -- Case split: f(0) = 0 or f(0) ≠ 0
  by_cases hf0 : f 0 = 0
  · -- Case B: f(0) = 0
    -- f(z) = z^n h(z) with h(0) ≠ 0, n ≥ 1
    -- |h(z)| ≥ |z|^{3/2 - n} for z ≠ 0
    -- If n ≥ 2: |h(z)| ≥ |z|^{-1/2} → ∞ as z → 0, contradicting h continuous
    -- If n = 1: reduce to Case A applied to h
    sorry
  · -- Case A: f(0) ≠ 0
    -- f never vanishes
    have hf_ne : ∀ z, f z ≠ 0 := by
      intro z
      by_cases hz : z = 0
      · rw [hz]; exact hf0
      · exact nonzero_of_lower_bound f hbound z hz
    -- 1/f is entire
    have hinv_diff : Differentiable ℂ (fun z => (f z)⁻¹) :=
      Differentiable.inv hf_diff hf_ne
    -- 1/f is bounded: |1/f(z)| ≤ 1 for |z| ≥ 1, and continuous (hence bounded)
    -- on compact {|z| ≤ 1}
    -- For |z| ≥ 1: proven above
    -- For |z| ≤ 1: need compactness argument
    sorry

end ApmCanaries.A94J08
