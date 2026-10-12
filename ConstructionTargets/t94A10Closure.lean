import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-! Reusable calculations for the solid-angle form on punctured three-space. -/

noncomputable section
namespace ConstructionTargets.T94A10Closure

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The standard determinant volume form on Euclidean three-space. -/
def volumeForm : E3 [⋀^Fin 3]→L[ℝ] ℝ where
  toAlternatingMap := Matrix.detRowAlternating.compLinearMap
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toLinearMap
  cont := by
    change Continuous (fun v : Fin 3 → E3 => Matrix.det (fun i j => v i j))
    fun_prop

/-- The ambient solid-angle two-form: contraction of the volume form with
the radial vector, scaled by the inverse cube of the radius. -/
def solidAngleAmbient (x : E3) : E3 [⋀^Fin 2]→L[ℝ] ℝ :=
  (‖x‖ ^ 3)⁻¹ • volumeForm.curryLeft x

/-- The scalar radial coefficient of the solid-angle form. -/
def radialInvCube (x : E3) : ℝ := (‖x‖ ^ 3)⁻¹

/-- Coordinate expansion of the ambient solid-angle form. -/
theorem solidAngleAmbient_apply (x : E3) (v : Fin 2 → E3) :
    solidAngleAmbient x v =
      (x 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) -
        x 1 * (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
        x 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) / ‖x‖ ^ 3 := by
  change (‖x‖ ^ 3)⁻¹ * Matrix.det
      (Matrix.vecCons (fun j => x j) (fun i j => v i j)) = _
  simp [Matrix.det_fin_three]
  ring

/-- The norm denominator agrees with the coordinate square-root denominator
used by the frozen problem. -/
theorem norm_cube_eq_coordinate_denominator (x : E3) :
    ‖x‖ ^ 3 = (Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) ^ 3 := by
  congr 1
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_succ]
  ring

/-- Exact coordinate formula used by the frozen `IsOmega` predicate. -/
theorem solidAngleAmbient_apply_coordinate (x : E3) (v : Fin 2 → E3) :
    solidAngleAmbient x v =
      (x 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) -
        x 1 * (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
        x 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) /
      (Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) ^ 3 := by
  rw [solidAngleAmbient_apply, norm_cube_eq_coordinate_denominator]

/-- Derivative of the inverse-cube radial coefficient away from the origin. -/
theorem hasFDerivAt_radialInvCube (x : E3) (hx : x ≠ 0) :
    HasFDerivAt radialInvCube
      ((-3 * ‖x‖⁻¹ ^ 5) • innerSL ℝ x) x := by
  have hnorm : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  have hsq : HasFDerivAt (fun y : E3 => ‖y‖ ^ 2)
      (2 • innerSL ℝ x) x := by
    simpa using (hasFDerivAt_id x).norm_sq
  have hsqrt := (Real.hasDerivAt_sqrt (pow_ne_zero 2 hnorm)).comp_hasFDerivAt x hsq
  have hn : HasFDerivAt (fun y : E3 => ‖y‖)
      ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x)) x := by
    convert hsqrt using 1
    · funext y
      simp [Real.sqrt_sq (norm_nonneg y)]
    · rw [Real.sqrt_sq (norm_nonneg x)]
  have hcub := hn.pow 3
  have hinv := (hasDerivAt_inv (pow_ne_zero 3 hnorm)).comp_hasFDerivAt x hcub
  convert hinv using 1
  ext u
  simp only [ContinuousLinearMap.smul_apply, nsmul_eq_mul,
    one_div, innerSL_apply_apply]
  simp only [smul_eq_mul]
  field_simp [hnorm]
  ring

#print axioms solidAngleAmbient_apply
#print axioms norm_cube_eq_coordinate_denominator
#print axioms solidAngleAmbient_apply_coordinate
#print axioms hasFDerivAt_radialInvCube

end ConstructionTargets.T94A10Closure
