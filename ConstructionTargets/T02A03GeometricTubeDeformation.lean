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

theorem continuous_rightTubePlanarComplex : Continuous rightTubePlanarComplex := by
  unfold rightTubePlanarComplex
  fun_prop

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

theorem rightTubePlanarComplex_re_pos
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_rightTube) :
    0 < (rightTubePlanarComplex p).re := by
  obtain ⟨q, ⟨t, rfl⟩, hd⟩ := rightTube_exists_near_rightCore p hp
  have hcoord := PiLp.dist_apply_le p (apm_t02a03_rightCore t) 0
  have hq0 : 0 ≤ apm_t02a03_rightCore t 0 := by
    simp [apm_t02a03_rightCore]
    exact Real.cos_le_one t
  rw [Real.dist_eq] at hcoord
  have habs : |p 0 - apm_t02a03_rightCore t 0| ≤ (1 / 4 : ℝ) :=
    hcoord.trans hd
  have hp0 : -(1 / 4 : ℝ) ≤ p 0 := by
    have hlo := (abs_le.mp habs).1
    linarith
  simp [rightTubePlanarComplex]
  linarith

noncomputable def rightTubePlanarInterpolation
    (tp : unitInterval × RightTubeMinusLeftCore) : ℂ :=
  ((1 - (tp.1 : ℝ) : ℝ) : ℂ) +
    ((tp.1 : ℝ) : ℂ) * rightTubePlanarComplex tp.2.1

theorem rightTubePlanarInterpolation_ne_zero
    (tp : unitInterval × RightTubeMinusLeftCore) :
    rightTubePlanarInterpolation tp ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hs0 : 0 ≤ (tp.1 : ℝ) := tp.1.2.1
  have hs1 : (tp.1 : ℝ) ≤ 1 := tp.1.2.2
  have hp := rightTubePlanarComplex_re_pos tp.2.1 tp.2.2.1
  simp [rightTubePlanarInterpolation] at hre
  by_cases hs : (tp.1 : ℝ) = 1
  · rw [hs] at hre
    nlinarith
  · have hslt : (tp.1 : ℝ) < 1 := lt_of_le_of_ne hs1 hs
    have hmul : 0 ≤ (tp.1 : ℝ) * (rightTubePlanarComplex tp.2.1).re :=
      mul_nonneg hs0 hp.le
    nlinarith

theorem continuous_rightTubePlanarInterpolation :
    Continuous rightTubePlanarInterpolation := by
  unfold rightTubePlanarInterpolation
  apply Continuous.add
  · fun_prop
  · apply Continuous.mul
    · fun_prop
    · exact continuous_rightTubePlanarComplex.comp
        (continuous_subtype_val.comp continuous_snd)

noncomputable def rightTubePlanarRotation :
    C(unitInterval × RightTubeMinusLeftCore, Circle) where
  toFun tp := ⟨NormedSpace.normalize (rightTubePlanarInterpolation tp),
    mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize (rightTubePlanarInterpolation_ne_zero tp))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro tp
    exact ((continuous_norm.comp continuous_rightTubePlanarInterpolation).continuousAt.inv₀
      (norm_ne_zero_iff.mpr (rightTubePlanarInterpolation_ne_zero tp))).smul
        continuous_rightTubePlanarInterpolation.continuousAt

theorem rightTubePlanarRotation_zero (p : RightTubeMinusLeftCore) :
    (rightTubePlanarRotation (0, p) : ℂ) = 1 := by
  simp [rightTubePlanarRotation, rightTubePlanarInterpolation,
    NormedSpace.normalize_eq_self_of_norm_eq_one]

theorem rightTubePlanarRotation_one (p : RightTubeMinusLeftCore) :
    (rightTubePlanarRotation (1, p) : ℂ) =
      NormedSpace.normalize (rightTubePlanarComplex p.1) := by
  simp [rightTubePlanarRotation, rightTubePlanarInterpolation]

theorem rightTubePlanarRotation_exists :
    ∃ R : C(unitInterval × RightTubeMinusLeftCore, Circle),
      (∀ p, (R (0, p) : ℂ) = 1) ∧
      (∀ p, (R (1, p) : ℂ) =
        NormedSpace.normalize (rightTubePlanarComplex p.1)) := by
  exact ⟨rightTubePlanarRotation, rightTubePlanarRotation_zero,
    rightTubePlanarRotation_one⟩

noncomputable def rightTubePolarReconstruction
    (u : Circle) (n : ℂ) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![-1 + (1 + n.re) * (u : ℂ).re,
    (1 + n.re) * (u : ℂ).im, n.im]

theorem rightTubePolarReconstruction_self
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_rightTube) :
    rightTubePolarReconstruction
      ⟨NormedSpace.normalize (rightTubePlanarComplex p),
        mem_sphere_zero_iff_norm.mpr
          (NormedSpace.norm_normalize
            (rightTubePlanarComplex_ne_zero p hp))⟩
      (rightTubeNormalComplex p) = p := by
  have hscale := NormedSpace.norm_smul_normalize (rightTubePlanarComplex p)
  have hre : ‖rightTubePlanarComplex p‖ *
      (NormedSpace.normalize (rightTubePlanarComplex p)).re =
      (rightTubePlanarComplex p).re := by
    have h := congrArg Complex.re hscale
    exact (RCLike.smul_re ‖rightTubePlanarComplex p‖
      (NormedSpace.normalize (rightTubePlanarComplex p))).symm.trans h
  have him : ‖rightTubePlanarComplex p‖ *
      (NormedSpace.normalize (rightTubePlanarComplex p)).im =
      (rightTubePlanarComplex p).im := by
    have h := congrArg Complex.im hscale
    exact (RCLike.smul_im ‖rightTubePlanarComplex p‖
      (NormedSpace.normalize (rightTubePlanarComplex p))).symm.trans h
  have hn : ‖(p 0 : ℂ) + 1 + (p 1 : ℂ) * Complex.I‖ =
      ‖rightTubePlanarComplex p‖ := by
    simp [rightTubePlanarComplex]
  ext i
  fin_cases i
  · have hpre : (rightTubePlanarComplex p).re = p 0 + 1 := by
      simp [rightTubePlanarComplex]
    simp [rightTubePolarReconstruction, rightTubeNormalComplex]
    rw [hn]
    linarith
  · have hpim : (rightTubePlanarComplex p).im = p 1 := by
      simp [rightTubePlanarComplex]
    simp [rightTubePolarReconstruction, rightTubeNormalComplex]
    rw [hn]
    linarith
  · simp [rightTubePolarReconstruction, rightTubeNormalComplex]

noncomputable def rightTubeCorePlanarComplex (p : apm_t02a03_E3) : ℂ :=
  ((1 - p 0 : ℝ) : ℂ) + (p 1 : ℂ) * Complex.I

theorem rightTubeCorePlanarComplex_ne_zero
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_rightTube) :
    rightTubeCorePlanarComplex p ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [rightTubeCorePlanarComplex] at hre him
  have hx : p 0 = 1 := by linarith
  have hy : p 1 = 0 := him
  obtain ⟨q, ⟨t, rfl⟩, hd⟩ := rightTube_exists_near_rightCore p hp
  rw [dist_eq_norm, EuclideanSpace.norm_eq] at hd
  simp [apm_t02a03_rightCore, hx, hy, Fin.sum_univ_succ] at hd
  have hs : 1 ≤ √(Real.cos t ^ 2 +
      (Real.sin t ^ 2 + p 2 ^ 2)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (p 2)]
  norm_num at hd
  linarith

noncomputable def rightTubeCoreNormalComplex (p : apm_t02a03_E3) : ℂ :=
  ((1 - ‖rightTubeCorePlanarComplex p‖ : ℝ) : ℂ) + (p 2 : ℂ) * Complex.I

noncomputable def rightTubeCorePolarReconstruction
    (u : Circle) (n : ℂ) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![1 - (1 - n.re) * (u : ℂ).re,
    (1 - n.re) * (u : ℂ).im, n.im]

theorem rightTubeCorePolarReconstruction_self
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_rightTube) :
    rightTubeCorePolarReconstruction
      ⟨NormedSpace.normalize (rightTubeCorePlanarComplex p),
        mem_sphere_zero_iff_norm.mpr
          (NormedSpace.norm_normalize
            (rightTubeCorePlanarComplex_ne_zero p hp))⟩
      (rightTubeCoreNormalComplex p) = p := by
  have hscale := NormedSpace.norm_smul_normalize (rightTubeCorePlanarComplex p)
  have hre : ‖rightTubeCorePlanarComplex p‖ *
      (NormedSpace.normalize (rightTubeCorePlanarComplex p)).re =
      (rightTubeCorePlanarComplex p).re := by
    have h := congrArg Complex.re hscale
    exact (RCLike.smul_re ‖rightTubeCorePlanarComplex p‖
      (NormedSpace.normalize (rightTubeCorePlanarComplex p))).symm.trans h
  have him : ‖rightTubeCorePlanarComplex p‖ *
      (NormedSpace.normalize (rightTubeCorePlanarComplex p)).im =
      (rightTubeCorePlanarComplex p).im := by
    have h := congrArg Complex.im hscale
    exact (RCLike.smul_im ‖rightTubeCorePlanarComplex p‖
      (NormedSpace.normalize (rightTubeCorePlanarComplex p))).symm.trans h
  ext i
  fin_cases i
  · have hpre : (rightTubeCorePlanarComplex p).re = 1 - p 0 := by
      simp [rightTubeCorePlanarComplex]
    simp [rightTubeCorePolarReconstruction, rightTubeCoreNormalComplex]
    linarith
  · have hpim : (rightTubeCorePlanarComplex p).im = p 1 := by
      simp [rightTubeCorePlanarComplex]
    simp [rightTubeCorePolarReconstruction, rightTubeCoreNormalComplex]
    linarith
  · simp [rightTubeCorePolarReconstruction, rightTubeCoreNormalComplex]

end ConstructionTargets.T02A03GeometricTubeDeformation

#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeNormalComplex_eq_zero_iff
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeMeridianCoordinate_circleMeridian
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.isCompact_range_rightCore
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubePlanarComplex_ne_zero
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubePlanarComplex_re_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubePlanarRotation_exists
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubePolarReconstruction_self
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCorePlanarComplex_ne_zero
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCorePolarReconstruction_self
