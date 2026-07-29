import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Radial integration in `ℝ³`

Mathlib's `MeasureTheory.integral_fun_norm_addHaar` is the general polar
decomposition for a finite-dimensional real normed space with additive Haar
measure.  This file specializes it to Euclidean three-space and records the
coefficient `4π`.
-/

open MeasureTheory Metric Module Real Set
open scoped ENNReal

noncomputable section

namespace ConstructionTargets.RadialIntegrationR3

/-- Euclidean three-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- A radial function on `ℝ³` is integrable exactly when its one-dimensional
radial density `r² g(r)` is integrable on `(0, ∞)`. -/
theorem integrable_radial_R3_iff {g : ℝ → ℝ} :
    Integrable (fun x : E => g ‖x‖) volume ↔
      IntegrableOn (fun r : ℝ => r ^ 2 * g r) (Ioi 0) := by
  simpa only [E, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSubDiff,
    smul_eq_mul] using
    (MeasureTheory.integrable_fun_norm_addHaar
      (volume : Measure E) (f := g))

/-- `Lᵖ` membership for a radial function on `ℝ³` reduces to one-dimensional
integrability of `r² ‖g(r)‖ᵖ` on `(0, ∞)`. -/
theorem memLp_radial_R3_iff
    {g : ℝ → ℝ} {p : ℝ≥0∞}
    (hg : AEStronglyMeasurable (fun x : E => g ‖x‖) volume)
    (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    MemLp (fun x : E => g ‖x‖) p volume ↔
      IntegrableOn (fun r : ℝ => r ^ 2 * ‖g r‖ ^ p.toReal) (Ioi 0) := by
  rw [← integrable_norm_rpow_iff hg hp0 hp_top]
  simpa only [E, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSubDiff,
    smul_eq_mul] using
    (MeasureTheory.integrable_fun_norm_addHaar
      (volume : Measure E) (f := fun r : ℝ => ‖g r‖ ^ p.toReal))

/-- Radial integration in Euclidean three-space:

`∫ x, g ‖x‖ = 4π ∫₀∞ g(r) r² dr`.

The integrability hypothesis matches the downstream interface.  The underlying
Mathlib identity is valid for the Bochner integral without this hypothesis. -/
theorem radial_integral_R3 {g : ℝ → ℝ}
    (_hg : Integrable (fun x : E => g ‖x‖) volume) :
    ∫ x : E, g ‖x‖ ∂volume =
      4 * π * ∫ r in Ioi (0 : ℝ), g r * r ^ 2 ∂volume := by
  rw [MeasureTheory.integral_fun_norm_addHaar (volume : Measure E) g]
  simp only [E, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSubDiff,
    nsmul_eq_mul, smul_eq_mul]
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ π * 4 / 3)]
  have hmul :
      (fun y : ℝ => y ^ 2 * g y) = (fun y : ℝ => g y * y ^ 2) := by
    funext y
    ring
  rw [hmul]
  ring

end ConstructionTargets.RadialIntegrationR3
