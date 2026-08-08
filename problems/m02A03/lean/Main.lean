import Mathlib

/-!
# APM m02A03 — logarithmic fundamental solution in the Euclidean plane

The plane is encoded as `EuclideanSpace ℝ (Fin 2)`.  Thus the norm in the
logarithmic kernel is the Euclidean norm, while the Laplacian is the sum of
the two second coordinate derivatives.

## Statement repairs

The former encoding used `ℝ × ℝ`, whose Mathlib product norm is the sup norm.
It has been replaced by `EuclideanSpace ℝ (Fin 2)`, as required for the
two-dimensional Newtonian potential.

The printed Laplacian contains the typographical fragment `∂²_{x₁} += ∂²_{x₂}`;
this is read as the sum of the two second partial derivatives.

## Encoding questions

None.
-/

open MeasureTheory

abbrev APMM02A03Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def apm_m02a03_kernel
    (y x : APMM02A03Plane) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log ‖x - y‖

noncomputable def apm_m02a03_laplacian
    (φ : APMM02A03Plane → ℝ) (x : APMM02A03Plane) : ℝ :=
  ∑ i : Fin 2,
    deriv
      (fun t => deriv
        (fun s => φ (x + (s - x i) • EuclideanSpace.single i 1)) t)
      (x i)

theorem apm_m02a03 (y : APMM02A03Plane) :
    LocallyIntegrable (apm_m02a03_kernel y) volume ∧
    ∀ φ : APMM02A03Plane → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∫ x, apm_m02a03_kernel y x * apm_m02a03_laplacian φ x) = φ y := by
  sorry
