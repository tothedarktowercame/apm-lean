import ConstructionTargets.T02A03GeometricTubeCover
import ConstructionTargets.T02A03LeftTubePuncturedModel
import ConstructionTargets.TorusCircleWedgeOpenCover

noncomputable section

namespace ConstructionTargets.T02A03GeometricTubeDeformation

open ConstructionTargets.T02A03GeometricTubeCover

abbrev GeometricY := apm_t02a03_geometricY_probe

abbrev GenericWedge :=
  ConstructionTargets.TorusCircleWedgeOpenCover.GenericWedge

/-- The second closed tube piece after imposing the frozen deletion. -/
abbrev RightTubeMinusLeftCore :=
  {p : apm_t02a03_E3 //
    p ∈ apm_t02a03_rightTube ∧ p ∉ Set.range apm_t02a03_leftCore}

/-- The radial defect in the first two coordinates, together with height as
the imaginary coordinate. -/
noncomputable def rightTubeNormalComplex (p : apm_t02a03_E3) : ℂ :=
  (‖((p 0 + 1 : ℝ) : ℂ) + (p 1 : ℂ) * Complex.I‖ - 1 : ℂ) +
    (p 2 : ℂ) * Complex.I

/-- The ambient normal coordinate vanishes exactly on the frozen left core. -/
theorem rightTubeNormalComplex_eq_zero_iff (p : apm_t02a03_E3) :
    rightTubeNormalComplex p = 0 ↔ p ∈ Set.range apm_t02a03_leftCore := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [rightTubeNormalComplex] at hre him
    let w : ℂ := ((p 0 + 1 : ℝ) : ℂ) + (p 1 : ℂ) * Complex.I
    have hw : ‖w‖ = 1 := by simpa [w] using sub_eq_zero.mp hre
    have hw0 : w ≠ 0 := by
      intro h0
      simp [h0] at hw
    refine ⟨Complex.arg w, ?_⟩
    ext i
    fin_cases i
    · have hc := Complex.cos_arg hw0
      rw [hw, div_one] at hc
      simp [apm_t02a03_leftCore, w] at hc ⊢
      linarith
    · have hs := Complex.sin_arg w
      rw [hw, div_one] at hs
      simpa [apm_t02a03_leftCore, w] using hs
    · simpa [apm_t02a03_leftCore] using him.symm
  · rintro ⟨t, rfl⟩
    have hu : ‖((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_def]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add]
      rw [show Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 by
        nlinarith [Real.sin_sq_add_cos_sq t]]
      norm_num
    apply Complex.ext
    · simpa [rightTubeNormalComplex, apm_t02a03_leftCore] using
        sub_eq_zero.mpr hu
    · simp [rightTubeNormalComplex, apm_t02a03_leftCore]

theorem continuous_rightTubeNormalComplex : Continuous rightTubeNormalComplex := by
  unfold rightTubeNormalComplex
  fun_prop

/-- Normalize the nonzero ambient normal coordinate on the deleted right
tube. -/
noncomputable def rightTubeMeridianCoordinate :
    C(RightTubeMinusLeftCore, Circle) where
  toFun p := ⟨NormedSpace.normalize (rightTubeNormalComplex p.1),
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (by
      exact fun h => p.2.2 ((rightTubeNormalComplex_eq_zero_iff p.1).mp h)))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro p
    have hz : Continuous (fun q : RightTubeMinusLeftCore =>
        rightTubeNormalComplex q.1) :=
      continuous_rightTubeNormalComplex.comp continuous_subtype_val
    exact ((continuous_norm.comp hz).continuousAt.inv₀
      (norm_ne_zero_iff.mpr (fun h =>
        p.2.2 ((rightTubeNormalComplex_eq_zero_iff p.1).mp h)))).smul
          hz.continuousAt

/-- The normalized normal coordinate is a left inverse to the frozen
meridian parametrization. -/
theorem rightTubeMeridianCoordinate_circleMeridian
    (z : Circle)
    (hz : apm_t02a03_circleMeridian z ∈ apm_t02a03_rightTube ∧
      apm_t02a03_circleMeridian z ∉ Set.range apm_t02a03_leftCore) :
    rightTubeMeridianCoordinate ⟨apm_t02a03_circleMeridian z, hz⟩ = z := by
  apply Subtype.ext
  change NormedSpace.normalize (rightTubeNormalComplex
    (apm_t02a03_circleMeridian z)) = (z : ℂ)
  have habs : |(z : ℂ).re| ≤ 1 := by
    simpa [Circle.norm_coe z] using (RCLike.abs_re_le_norm (z : ℂ))
  have hre : -(1 : ℝ) ≤ (z : ℂ).re := (abs_le.mp habs).1
  have hpos : 0 < (1 / 8 : ℝ) := by norm_num
  rw [show rightTubeNormalComplex (apm_t02a03_circleMeridian z) =
      (1 / 8 : ℝ) • (z : ℂ) by
    apply Complex.ext
    · simp [rightTubeNormalComplex, apm_t02a03_circleMeridian,
        Complex.norm_def, Complex.normSq_apply]
      rw [show (8⁻¹ * (z : ℂ).re + 1) * (8⁻¹ * (z : ℂ).re + 1) =
        (8⁻¹ * (z : ℂ).re + 1) ^ 2 by ring]
      rw [Real.sqrt_sq (by norm_num at hre ⊢; linarith)]
      ring
    · simp [rightTubeNormalComplex, apm_t02a03_circleMeridian]]
  exact (NormedSpace.normalize_smul_of_pos hpos (z : ℂ)).trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (Circle.norm_coe z))

noncomputable def rightCoreCircle (z : Circle) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![1 - (z : ℂ).re, (z : ℂ).im, 0]

theorem continuous_rightCoreCircle : Continuous rightCoreCircle := by
  unfold rightCoreCircle
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem range_rightCoreCircle :
    Set.range rightCoreCircle = Set.range apm_t02a03_rightCore := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨Complex.arg (z : ℂ), ?_⟩
    ext i
    fin_cases i
    · simpa [rightCoreCircle, apm_t02a03_rightCore,
        Circle.norm_coe] using Complex.cos_arg (Circle.coe_ne_zero z)
    · simpa [rightCoreCircle, apm_t02a03_rightCore,
        Circle.norm_coe] using Complex.sin_arg (z : ℂ)
    · simp [rightCoreCircle, apm_t02a03_rightCore]
  · rintro ⟨t, rfl⟩
    refine ⟨Circle.exp t, ?_⟩
    ext i
    fin_cases i <;> simp [rightCoreCircle, apm_t02a03_rightCore]

theorem isCompact_range_rightCore :
    IsCompact (Set.range apm_t02a03_rightCore) := by
  rw [← range_rightCoreCircle]
  exact isCompact_range continuous_rightCoreCircle

theorem rightTube_exists_near_rightCore
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_rightTube) :
    ∃ q ∈ Set.range apm_t02a03_rightCore, dist p q ≤ (1 / 4 : ℝ) := by
  rw [apm_t02a03_rightTube,
    isCompact_range_rightCore.cthickening_eq_biUnion_closedBall
      (by norm_num)] at hp
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hp
  rcases hp with ⟨q, hq, hd⟩
  exact ⟨q, hq, by simpa [dist_comm] using hd⟩

noncomputable def rightTubePlanarComplex (p : apm_t02a03_E3) : ℂ :=
  ((p 0 + 1 : ℝ) : ℂ) + (p 1 : ℂ) * Complex.I

theorem rightTubePlanarComplex_ne_zero
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_rightTube) :
    rightTubePlanarComplex p ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [rightTubePlanarComplex] at hre him
  have hx : p 0 = -1 := by linarith
  have hy : p 1 = 0 := him
  obtain ⟨q, ⟨t, rfl⟩, hd⟩ := rightTube_exists_near_rightCore p hp
  rw [dist_eq_norm, EuclideanSpace.norm_eq] at hd
  simp [apm_t02a03_rightCore, hx, hy, Fin.sum_univ_succ] at hd
  have hs : 1 ≤ √((-2 + Real.cos t) ^ 2 +
      (Real.sin t ^ 2 + p 2 ^ 2)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have hc : Real.cos t ≤ 1 := Real.cos_le_one t
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (p 2)]
  have hd' : √((-2 + Real.cos t) ^ 2 +
      (Real.sin t ^ 2 + p 2 ^ 2)) ≤ (1 / 4 : ℝ) := by
    simpa [show (-1 : ℝ) - (1 - Real.cos t) = -2 + Real.cos t by ring]
      using hd
  norm_num at hd'
  linarith

end ConstructionTargets.T02A03GeometricTubeDeformation

#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeNormalComplex_eq_zero_iff
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeMeridianCoordinate_circleMeridian
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.isCompact_range_rightCore
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubePlanarComplex_ne_zero
