import Mathlib

/-!
# APM m02A03 — logarithmic fundamental solution in the plane

## Statement repairs

The printed Laplacian contains the typographical fragment `∂²_{x₁} += ∂²_{x₂}`;
this is read as the sum of the two second partial derivatives.
-/

open Set MeasureTheory

noncomputable def apm_m02a03_kernel (y x : ℝ × ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log ‖x - y‖

noncomputable def apm_m02a03_laplacian
    (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  deriv (fun t => deriv (fun s => φ (s, x.2)) t) x.1 +
    deriv (fun t => deriv (fun s => φ (x.1, s)) t) x.2

theorem apm_m02a03 (y : ℝ × ℝ) :
    LocallyIntegrable (apm_m02a03_kernel y) volume ∧
    ∀ φ : ℝ × ℝ → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∫ x, apm_m02a03_kernel y x * apm_m02a03_laplacian φ x) = φ y := by
  sorry
