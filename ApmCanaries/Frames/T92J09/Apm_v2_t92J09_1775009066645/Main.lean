import Mathlib
import ApmCanaries.Frames.T92J09.Apm_v2_t92J09_1775009066645.Scratch

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory Metric ENNReal Real

namespace ApmCanaries.Frames.T92J09.Apm_v2_t92J09_1775009066645.Main

/-- The measure of the unit ball in `ℝ^3` equals `4π/3`; this value matches the
right-hand side of the Stokes computation for the form `ω = x dy ∧ dz`. -/
theorem integral_form_on_sphere :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal =
      (4 / 3 : ℝ) * Real.pi := by
  have hvol :=
    EuclideanSpace.volume_ball_fin_three (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ)
  have hone : (ENNReal.ofReal (1 : ℝ)) ^ (3 : ℕ) = (1 : ENNReal) := by
    simpa using (one_pow (3 : ℕ) : (1 : ENNReal) ^ 3 = 1)
  have hπ : Real.pi * 4 / 3 = (4 / 3 : ℝ) * Real.pi := by
    field_simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hvol' : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi) := by
    simpa [hone, hπ, one_mul] using hvol
  have hpos : 0 ≤ (4 / 3 : ℝ) * Real.pi := by
    have : (0 : ℝ) ≤ 4 / 3 := by norm_num
    exact mul_nonneg this Real.pi_nonneg
  have := congrArg ENNReal.toReal hvol'
  simpa [ENNReal.toReal_ofReal, hpos] using this

end ApmCanaries.Frames.T92J09.Apm_v2_t92J09_1775009066645.Main
