import Mathlib

/-!
# APM m96J03

## Statement repairs

The condition `f(x)=0` when `‖x‖>0` is corrected to `‖x‖>1`.
As printed, the two clauses overlap throughout `0 < ‖x‖ ≤ 1`; the correction
makes `f` the unit-ball indicator used by the supplied solution.

## Encoding questions

The distributional Laplacian is stated in its exact weak form: for every test
function φ, ∫ f Δφ = ∫_{S^{n-1}} ∂φ/∂ν dσ, i.e. Δf = −(∂/∂ν)(δ_{S^{n-1}}).
The outward normal at ω on the unit sphere is ω itself.

Surface measure σ is `volume.toSphere` (Mathlib's polar-coordinates measure:
σ(s) = n · vol{r ω : 0 < r < 1, ω ∈ s}, total mass n·vol(B) = |S^{n-1}|).
Until 2026-09-30 this was raw `μH[n-1]` on `Metric.sphere 0 1`. Mathlib's μH
is unnormalised (sum of diam^d), so for n = 3 it gives the unit sphere mass 16
rather than 4π, and the identity was false for n ≥ 3 (solve-loop strategy
note, 2026-09-30).
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

/-- The frozen coordinate Laplacian vanishes on constant functions. -/
lemma apm_m96j03_laplacian_const {n : ℕ} (c : ℝ) (x : apm_m96j03_E n) :
    apm_m96j03_laplacian (fun _ ↦ c) x = 0 := by
  simp [apm_m96j03_laplacian]

/-- Under the smoothness available in the theorem, each frozen coordinate
term is exactly the corresponding diagonal value of the second iterated
Fréchet derivative. -/
lemma apm_m96j03_coordinate_second_derivative {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : apm_m96j03_E n) (i : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) =
      iteratedFDeriv ℝ 2 φ x
        ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] := by
  have h2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd x) (by fun_prop)]
  simp [iteratedFDeriv_two_apply]

/-- The unit-ball indicator is measurable; this is needed before any
Gauss--Green approximation or dominated-convergence argument. -/
lemma apm_m96j03_measurable_ballIndicator {n : ℕ} :
    Measurable (apm_m96j03_ballIndicator : apm_m96j03_E n → ℝ) := by
  unfold apm_m96j03_ballIndicator
  have hmeas : Measurable fun x : apm_m96j03_E n ↦
      Set.indicator (Metric.closedBall 0 1) (fun _ ↦ (1 : ℝ)) x :=
    measurable_const.indicator measurableSet_closedBall
  convert hmeas using 1
  funext x
  simp [Set.indicator, Metric.mem_closedBall, dist_zero_right]

def apm_m96j03_IsTestFunction {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

/-- The volume term in the weak Laplacian identity is exactly the integral
over the closed unit ball. -/
lemma apm_m96j03_integral_ballIndicator {n : ℕ}
    (g : apm_m96j03_E n → ℝ) :
    (∫ x, apm_m96j03_ballIndicator x * g x) =
      ∫ x in Metric.closedBall 0 1, g x := by
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [Set.indicator, apm_m96j03_ballIndicator, Metric.mem_closedBall,
    dist_zero_right]
  split_ifs <;> simp

theorem apm_m96j03
    (n : ℕ) (φ : apm_m96j03_E n → ℝ)
    (hφ : apm_m96j03_IsTestFunction φ) :
    (∫ x : apm_m96j03_E n,
        apm_m96j03_ballIndicator x * apm_m96j03_laplacian φ x) =
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ φ ω ω ∂(volume.toSphere) := by
  rw [apm_m96j03_integral_ballIndicator]
  sorry
