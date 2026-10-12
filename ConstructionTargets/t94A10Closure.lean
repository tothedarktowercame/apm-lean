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

@[simp] theorem volumeForm_apply (v : Fin 3 → E3) :
    volumeForm v = Matrix.det (fun i j => v i j) := rfl

/-- The ambient solid-angle two-form: contraction of the volume form with
the radial vector, scaled by the inverse cube of the radius. -/
def solidAngleAmbient (x : E3) : E3 [⋀^Fin 2]→L[ℝ] ℝ :=
  (‖x‖ ^ 3)⁻¹ • volumeForm.curryLeft x

/-- The scalar radial coefficient of the solid-angle form. -/
def radialInvCube (x : E3) : ℝ := (‖x‖ ^ 3)⁻¹

/-- The unscaled contraction with the radial vector. -/
def radialNumerator (x : E3) : E3 [⋀^Fin 2]→L[ℝ] ℝ :=
  volumeForm.curryLeft x

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

/-- The unscaled radial contraction is linear in its base point. -/
theorem hasFDerivAt_radialNumerator (x : E3) :
    HasFDerivAt radialNumerator volumeForm.curryLeft x := by
  simpa [radialNumerator] using volumeForm.curryLeft.hasFDerivAt

/-- Product-rule derivative of the ambient solid-angle form. -/
theorem hasFDerivAt_solidAngleAmbient (x : E3) (hx : x ≠ 0) :
    HasFDerivAt solidAngleAmbient
      ((radialInvCube x) • volumeForm.curryLeft +
        (((-3 * ‖x‖⁻¹ ^ 5) • innerSL ℝ x).smulRight
          (volumeForm.curryLeft x))) x := by
  simpa [solidAngleAmbient, radialInvCube, radialNumerator] using
    (hasFDerivAt_radialInvCube x hx).smul (hasFDerivAt_radialNumerator x)

/-- The ambient solid-angle form is closed away from the origin. -/
theorem solidAngleAmbient_closed (x : E3) (hx : x ≠ 0) :
    DifferentiableAt ℝ solidAngleAmbient x ∧ extDeriv solidAngleAmbient x = 0 := by
  have hd := hasFDerivAt_solidAngleAmbient x hx
  refine ⟨hd.differentiableAt, ?_⟩
  ext v
  rw [extDeriv_apply hd.differentiableAt]
  simp_rw [(hd.continuousAlternatingMap_apply_const _).fderiv]
  simp only [ContinuousLinearMap.flipAlternating_apply_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  simp [Fin.sum_univ_three, volumeForm_apply, Matrix.det_fin_three, Fin.removeNth,
    Fin.succAbove, PiLp.inner_apply, real_inner_eq_re_inner]
  have hn : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  rw [show radialInvCube x = ‖x‖⁻¹ ^ 3 by simp [radialInvCube]]
  field_simp [hn]
  ring_nf
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]
  ring

/-- Latitude-longitude parametrization of the unit sphere. -/
def sphereParam (p : ℝ × ℝ) : E3 :=
  WithLp.toLp 2 ![Real.sin p.1 * Real.cos p.2,
    Real.sin p.1 * Real.sin p.2,
    Real.cos p.1]

/-- The latitude tangent of `sphereParam`. -/
def sphereParamLat (p : ℝ × ℝ) : E3 :=
  WithLp.toLp 2 ![Real.cos p.1 * Real.cos p.2,
    Real.cos p.1 * Real.sin p.2,
    -Real.sin p.1]

/-- The longitude tangent of `sphereParam`. -/
def sphereParamLong (p : ℝ × ℝ) : E3 :=
  WithLp.toLp 2 ![-Real.sin p.1 * Real.sin p.2,
    Real.sin p.1 * Real.cos p.2,
    0]

theorem sphereParam_differentiable : Differentiable ℝ sphereParam := by
  have hg : Differentiable ℝ (fun p : ℝ × ℝ =>
      ![Real.sin p.1 * Real.cos p.2,
        Real.sin p.1 * Real.sin p.2,
        Real.cos p.1]) := by
    rw [differentiable_pi]
    intro i
    fin_cases i <;> simp <;> fun_prop
  simpa [sphereParam] using
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.differentiable.comp
      hg

theorem hasDerivAt_sphereParam_lat (s t : ℝ) :
    HasDerivAt (fun u => sphereParam (u, t)) (sphereParamLat (s, t)) s := by
  have hg : HasDerivAt (fun u : ℝ =>
      ![Real.sin u * Real.cos t, Real.sin u * Real.sin t, Real.cos u])
      ![Real.cos s * Real.cos t, Real.cos s * Real.sin t, -Real.sin s] s := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using (Real.hasDerivAt_sin s).mul_const (Real.cos t)
    · simpa using (Real.hasDerivAt_sin s).mul_const (Real.sin t)
    · simpa using Real.hasDerivAt_cos s
  simpa [sphereParam, sphereParamLat] using
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp s
      hg.hasFDerivAt).hasDerivAt

theorem hasDerivAt_sphereParam_long (s t : ℝ) :
    HasDerivAt (fun u => sphereParam (s, u)) (sphereParamLong (s, t)) t := by
  have hg : HasDerivAt (fun u : ℝ =>
      ![Real.sin s * Real.cos u, Real.sin s * Real.sin u, Real.cos s])
      ![-Real.sin s * Real.sin t, Real.sin s * Real.cos t, 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa [mul_neg] using (Real.hasDerivAt_cos t).const_mul (Real.sin s)
    · simpa using (Real.hasDerivAt_sin t).const_mul (Real.sin s)
    · simpa using hasDerivAt_const t (Real.cos s)
  simpa [sphereParam, sphereParamLong] using
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp t
      hg.hasFDerivAt).hasDerivAt

theorem sphereParam_norm (p : ℝ × ℝ) : ‖sphereParam p‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [sphereParam, Fin.sum_univ_three]
  nlinarith [Real.sin_sq_add_cos_sq p.1, Real.sin_sq_add_cos_sq p.2]

theorem sphereParam_ne_zero (p : ℝ × ℝ) : sphereParam p ≠ 0 := by
  intro h
  have := sphereParam_norm p
  rw [h, norm_zero] at this
  norm_num at this

theorem sphereParam_add_two_pi (p : ℝ × ℝ) :
    sphereParam (p.1, p.2 + 2 * Real.pi) = sphereParam p := by
  ext i
  fin_cases i <;> simp [sphereParam]

theorem sphereParamLat_add_two_pi (p : ℝ × ℝ) :
    sphereParamLat (p.1, p.2 + 2 * Real.pi) = sphereParamLat p := by
  ext i
  fin_cases i <;> simp [sphereParamLat]

theorem sphereParamLong_add_two_pi (p : ℝ × ℝ) :
    sphereParamLong (p.1, p.2 + 2 * Real.pi) = sphereParamLong p := by
  ext i
  fin_cases i <;> simp [sphereParamLong]

theorem sphereParamLong_zero (t : ℝ) : sphereParamLong (0, t) = 0 := by
  ext i
  fin_cases i <;> simp [sphereParamLong]

theorem sphereParamLong_pi (t : ℝ) : sphereParamLong (Real.pi, t) = 0 := by
  ext i
  fin_cases i <;> simp [sphereParamLong]

/-- The solid-angle form evaluates to the spherical area coefficient on the
ordered latitude-longitude tangents. -/
theorem solidAngleAmbient_sphereParam (p : ℝ × ℝ) :
    solidAngleAmbient (sphereParam p) ![sphereParamLat p, sphereParamLong p] =
      Real.sin p.1 := by
  rw [solidAngleAmbient_apply, sphereParam_norm]
  simp [sphereParam, sphereParamLat, sphereParamLong]
  rw [show
    Real.sin p.1 * Real.cos p.2 * (Real.sin p.1 * (Real.sin p.1 * Real.cos p.2)) +
          Real.sin p.1 * Real.sin p.2 * (Real.sin p.1 * (Real.sin p.1 * Real.sin p.2)) +
        Real.cos p.1 *
          (Real.cos p.1 * Real.cos p.2 * (Real.sin p.1 * Real.cos p.2) +
            Real.cos p.1 * Real.sin p.2 * (Real.sin p.1 * Real.sin p.2)) =
      Real.sin p.1 * (Real.sin p.1 ^ 2 + Real.cos p.1 ^ 2) *
        (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) by ring]
  rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]
  ring

/-- Pullback coefficient for any form agreeing with the ambient solid-angle
form away from the origin. -/
theorem solidAngle_pullback_sphereParam
    (omega : E3 → E3 [⋀^Fin 2]→L[ℝ] ℝ)
    (homega : ∀ x, x ≠ 0 → omega x = solidAngleAmbient x) (p : ℝ × ℝ) :
    omega (sphereParam p) ![sphereParamLat p, sphereParamLong p] = Real.sin p.1 := by
  rw [homega _ (sphereParam_ne_zero p)]
  exact solidAngleAmbient_sphereParam p

#print axioms solidAngleAmbient_apply
#print axioms norm_cube_eq_coordinate_denominator
#print axioms solidAngleAmbient_apply_coordinate
#print axioms hasFDerivAt_radialInvCube
#print axioms hasFDerivAt_solidAngleAmbient
#print axioms solidAngleAmbient_closed
#print axioms sphereParam_norm
#print axioms sphereParam_add_two_pi
#print axioms solidAngleAmbient_sphereParam
#print axioms solidAngle_pullback_sphereParam

end ConstructionTargets.T94A10Closure
