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
  /-
  SKIPPED (frozen-statement defect). On `ℝ × ℝ`, Mathlib's product norm is
  the max norm, so the kernel is
  `log (max |x.1-y.1| |x.2-y.2|)`, not the Euclidean radial logarithm used
  by the source proof. On any open region away from `y` where
  `|x.1-y.1| > |x.2-y.2|`, this kernel equals `log |x.1-y.1|`; its classical
  Laplacian there is `-1 / (x.1-y.1)^2`, rather than zero. Choosing a
  nonnegative smooth test function compactly supported in such a region gives
  `φ y = 0` but, after ordinary integration by parts away from the pole, a
  nonzero pairing with the kernel. Hence the asserted distributional identity
  cannot hold.

  The intended theorem needs `EuclideanSpace ℝ (Fin 2)` (or an explicitly
  Euclidean norm under an isometry) in place of the product norm. The statement
  is frozen, so no repair was made.
  -/
  sorry
