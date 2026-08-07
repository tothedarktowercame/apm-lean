import Mathlib

open Filter MeasureTheory Set

noncomputable section

/-!
# APM a01A01

## Statement repairs

None.

## Encoding notes

The condition `∀ M N, ∃ k ≥ N, M ≤ f k x` is the cofinal quantified
characterization of `limsup (fun k ↦ f k x) = +∞`. The higher-dimensional
domain is the genuine Euclidean space `EuclideanSpace ℝ (Fin d)` with its
Lebesgue measure.
-/

theorem apm_a01a01 :
    (∃ f : ℕ → ℝ → ℝ,
      (∀ k, IntegrableOn (f k) (Icc (0 : ℝ) 1) volume) ∧
      (∀ k x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ f k x) ∧
      (∀ x, x ∈ Icc (0 : ℝ) 1 →
        ∀ M : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ M ≤ f k x) ∧
      Tendsto (fun k ↦ ∫ x in Icc (0 : ℝ) 1, f k x ∂volume)
        atTop (nhds 0)) ∧
    (∀ d : ℕ, 0 < d →
      ∃ f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ k, Integrable (f k) volume) ∧
        (∀ k x, 0 ≤ f k x) ∧
        (∀ x, ∀ M : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ M ≤ f k x) ∧
        Tendsto (fun k ↦ ∫ x, f k x ∂volume) atTop (nhds 0)) := by
  sorry
