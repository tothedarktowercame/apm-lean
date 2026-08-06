import Mathlib

/-!
# APM m96J03

## Statement repairs

The condition `f(x)=0` when `‖x‖>0` is corrected to `‖x‖>1`.
As printed, the two clauses overlap throughout `0 < ‖x‖ ≤ 1`; the correction
makes `f` the unit-ball indicator used by the supplied solution.

## Encoding questions

The distributional Laplacian is stated in its exact weak form. Surface measure
is `(n-1)`-dimensional Hausdorff measure restricted to the unit sphere, and the
outward normal there is the point `x` itself.
-/

open MeasureTheory
open scoped MeasureTheory

noncomputable section

abbrev apm_m96j03_E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def apm_m96j03_ballIndicator {n : ℕ} (x : apm_m96j03_E n) : ℝ :=
  if ‖x‖ ≤ 1 then 1 else 0

def apm_m96j03_laplacian {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (x : apm_m96j03_E n) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ
      (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)

def apm_m96j03_IsTestFunction {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

theorem apm_m96j03
    (n : ℕ) (φ : apm_m96j03_E n → ℝ)
    (hφ : apm_m96j03_IsTestFunction φ) :
    (∫ x : apm_m96j03_E n,
        apm_m96j03_ballIndicator x * apm_m96j03_laplacian φ x) =
      ∫ x : apm_m96j03_E n in Metric.sphere 0 1,
        fderiv ℝ φ x x ∂μH[(n - 1 : ℕ)] := by
  sorry
