import Mathlib

/-! # APM m03J03: examples and derivatives of distributions

## Statement repairs

None.  Mathlib's distribution convention uses real-valued test functions and
allows complex-valued distributions, which faithfully accommodates every part.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

noncomputable section

/-- The Heaviside function with the irrelevant value at zero chosen to be zero. -/
def m03J03Heaviside (x : ℝ) : ℝ := if 0 < x then 1 else 0

/-- The one-sided Dirac comb, polynomial-growth Fourier series, the two
distributional derivatives of `H sin`, and the absolute-value non-example. -/
theorem apm_m03j03 :
    (∃ T : Distribution (⊤ : Opens ℝ) ℂ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∑' n : ℕ, (φ n : ℂ)) ∧
    (∀ a : ℕ → ℂ, (∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
        ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N) →
      ∃ T : Distribution (⊤ : Opens ℝ) ℂ ⊤,
        ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
          HasSum (fun n : ℕ =>
            a n * (∫ x : ℝ,
              Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x)) (T φ)) ∧
    (∃ T DT D2T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∫ x : ℝ, m03J03Heaviside x * Real.sin x * φ x ∧
        DT φ = -∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * deriv φ x ∧
        DT φ = ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x ∧
        D2T φ = ∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * iteratedDeriv 2 φ x ∧
        D2T φ = φ 0 - T φ) ∧
    (¬ ∃ T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤, T φ = |φ 0|) := by
  sorry
