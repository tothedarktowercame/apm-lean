import ConstructionTargets.T02A03GeometricTubeCover
import ConstructionTargets.T02A03LeftTubePuncturedModel
import ConstructionTargets.TorusCircleWedgeOpenCover

noncomputable section

open scoped ComplexConjugate

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

theorem rightTubeCoreTubularCoordinates_continuous :
    Continuous rightTubeCoreNormalComplex ∧
      Continuous (Function.uncurry rightTubeCorePolarReconstruction) := by
  constructor
  · unfold rightTubeCoreNormalComplex rightTubeCorePlanarComplex
    fun_prop
  · unfold rightTubeCorePolarReconstruction Function.uncurry
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

noncomputable def rightTubeCoreAngularCoordinate :
    C(RightTubeMinusLeftCore, Circle) where
  toFun p := ⟨NormedSpace.normalize (rightTubeCorePlanarComplex p.1),
    mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize
        (rightTubeCorePlanarComplex_ne_zero p.1 p.2.1))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro p
    have hc : Continuous (fun q : RightTubeMinusLeftCore =>
        rightTubeCorePlanarComplex q.1) := by
      unfold rightTubeCorePlanarComplex
      fun_prop
    exact ((continuous_norm.comp hc).continuousAt.inv₀
      (norm_ne_zero_iff.mpr
        (rightTubeCorePlanarComplex_ne_zero p.1 p.2.1))).smul hc.continuousAt

noncomputable def rightTubeCoreNormalInterpolation
    (m : C(RightTubeMinusLeftCore, Circle)) :
    C(unitInterval × RightTubeMinusLeftCore, ℂ) where
  toFun tp :=
    ((1 - (tp.1 : ℝ) : ℝ) : ℂ) * rightTubeCoreNormalComplex
      (apm_t02a03_circleMeridian (m tp.2)) +
    ((tp.1 : ℝ) : ℂ) * rightTubeCoreNormalComplex tp.2.1
  continuous_toFun := by
    have hn := rightTubeCoreTubularCoordinates_continuous.1
    have hc : Continuous apm_t02a03_circleMeridian := by
      unfold apm_t02a03_circleMeridian
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop
    fun_prop

theorem rightTubeCoreNormalInterpolation_zero
    (m : C(RightTubeMinusLeftCore, Circle)) (p : RightTubeMinusLeftCore) :
    rightTubeCoreNormalInterpolation m (0, p) = rightTubeCoreNormalComplex
      (apm_t02a03_circleMeridian (m p)) := by
  simp [rightTubeCoreNormalInterpolation]

theorem rightTubeCoreNormalInterpolation_one
    (m : C(RightTubeMinusLeftCore, Circle)) (p : RightTubeMinusLeftCore) :
    rightTubeCoreNormalInterpolation m (1, p) = rightTubeCoreNormalComplex p.1 := by
  simp [rightTubeCoreNormalInterpolation]

theorem rightTubeCoreNormalInterpolation_exists :
    ∀ m : C(RightTubeMinusLeftCore, Circle),
      ∃ N : C(unitInterval × RightTubeMinusLeftCore, ℂ),
        (∀ p, N (0, p) = rightTubeCoreNormalComplex
          (apm_t02a03_circleMeridian (m p))) ∧
        (∀ p, N (1, p) = rightTubeCoreNormalComplex p.1) := by
  intro m
  exact ⟨rightTubeCoreNormalInterpolation m,
    rightTubeCoreNormalInterpolation_zero m,
    rightTubeCoreNormalInterpolation_one m⟩

theorem norm_rightTubeCoreNormalComplex_circleMeridian (z : Circle) :
    ‖rightTubeCoreNormalComplex (apm_t02a03_circleMeridian z)‖ = (1 / 8 : ℝ) := by
  have hzsq : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  have habs : |(z : ℂ).re| ≤ 1 := by
    simpa [Circle.norm_coe z] using (RCLike.abs_re_le_norm (z : ℂ))
  have hlo : -(1 : ℝ) ≤ (z : ℂ).re := (abs_le.mp habs).1
  have hhi : (z : ℂ).re ≤ 1 := (abs_le.mp habs).2
  rw [Complex.norm_def]
  simp [rightTubeCoreNormalComplex, rightTubeCorePlanarComplex,
    apm_t02a03_circleMeridian, Complex.norm_def, Complex.normSq_apply]
  have hsqrt : √((1 - 8⁻¹ * (z : ℂ).re) *
      (1 - 8⁻¹ * (z : ℂ).re)) = 1 - 8⁻¹ * (z : ℂ).re := by
    rw [← pow_two, Real.sqrt_sq (by norm_num at hlo hhi ⊢; linarith)]
  rw [hsqrt]
  have hinside :
      (1 - (1 - 8⁻¹ * (z : ℂ).re)) *
          (1 - (1 - 8⁻¹ * (z : ℂ).re)) +
        8⁻¹ * (z : ℂ).im * (8⁻¹ * (z : ℂ).im) = (1 / 64 : ℝ) := by
    norm_num at hzsq ⊢
    nlinarith
  rw [hinside]
  norm_num

theorem rightTubeCore_radial_error_le (p : apm_t02a03_E3) (t : ℝ) :
    |1 - ‖rightTubeCorePlanarComplex p‖| ≤
      ‖rightTubeCorePlanarComplex p -
        ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)‖ := by
  have hu : ‖((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_def]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add]
    rw [show Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 by
      nlinarith [Real.sin_sq_add_cos_sq t]]
    norm_num
  have h := abs_norm_sub_norm_le (rightTubeCorePlanarComplex p)
    ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)
  rw [hu] at h
  simpa [abs_sub_comm] using h

theorem rightTubeCoreInputNormalRadiusBound
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_rightTube) :
    ‖rightTubeCoreNormalComplex p‖ ≤ (1 / 4 : ℝ) := by
  obtain ⟨q, ⟨t, rfl⟩, hd⟩ := rightTube_exists_near_rightCore p hp
  have hr := rightTubeCore_radial_error_le p t
  have hnormplan : ‖rightTubeCorePlanarComplex p -
      ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)‖ =
      √((1 - p 0 - Real.cos t) ^ 2 + (p 1 - Real.sin t) ^ 2) := by
    rw [Complex.norm_def]
    simp only [rightTubeCorePlanarComplex, Complex.normSq_apply,
      Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, mul_one,
      zero_add]
    ring_nf
  rw [hnormplan] at hr
  rw [dist_eq_norm, EuclideanSpace.norm_eq] at hd
  simp [apm_t02a03_rightCore, Fin.sum_univ_succ] at hd
  rw [Complex.norm_def]
  simp [rightTubeCoreNormalComplex, Complex.normSq_apply]
  have hplan_nonneg : 0 ≤
      (1 - p 0 - Real.cos t) ^ 2 + (p 1 - Real.sin t) ^ 2 := by positivity
  have hsqrt_sq : (√((1 - p 0 - Real.cos t) ^ 2 +
      (p 1 - Real.sin t) ^ 2)) ^ 2 =
      (1 - p 0 - Real.cos t) ^ 2 + (p 1 - Real.sin t) ^ 2 := by
    exact (Real.sq_sqrt hplan_nonneg)
  have hrad_sq : (1 - ‖rightTubeCorePlanarComplex p‖) ^ 2 ≤
      (1 - p 0 - Real.cos t) ^ 2 + (p 1 - Real.sin t) ^ 2 := by
    have hsqrt_nonneg : 0 ≤ √((1 - p 0 - Real.cos t) ^ 2 +
        (p 1 - Real.sin t) ^ 2) := Real.sqrt_nonneg _
    have habs_sq : |1 - ‖rightTubeCorePlanarComplex p‖| ^ 2 =
        (1 - ‖rightTubeCorePlanarComplex p‖) ^ 2 := sq_abs _
    have hmul : 0 ≤
        (√((1 - p 0 - Real.cos t) ^ 2 + (p 1 - Real.sin t) ^ 2) -
          |1 - ‖rightTubeCorePlanarComplex p‖|) *
        (√((1 - p 0 - Real.cos t) ^ 2 + (p 1 - Real.sin t) ^ 2) +
          |1 - ‖rightTubeCorePlanarComplex p‖|) :=
      mul_nonneg (sub_nonneg.mpr hr)
        (add_nonneg hsqrt_nonneg (abs_nonneg _))
    nlinarith [sq_nonneg (1 - ‖rightTubeCorePlanarComplex p‖)]
  have hinside :
      (1 - ‖rightTubeCorePlanarComplex p‖) ^ 2 + p 2 ^ 2 ≤
      (p 0 - (1 - Real.cos t)) ^ 2 +
        ((p 1 - Real.sin t) ^ 2 + p 2 ^ 2) := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hinside
  simpa [pow_two] using hsqrt.trans hd

/-- Points of the right tube have planar core coordinate in the closed
quarter-thick annulus about the unit circle. -/
theorem rightTubeCorePlanarNormBounds
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_rightTube) :
    (3 / 4 : ℝ) ≤ ‖rightTubeCorePlanarComplex p‖ ∧
      ‖rightTubeCorePlanarComplex p‖ ≤ (5 / 4 : ℝ) := by
  have hn := rightTubeCoreInputNormalRadiusBound p hp
  have hre :
      |(rightTubeCoreNormalComplex p).re| ≤
        ‖rightTubeCoreNormalComplex p‖ :=
    RCLike.abs_re_le_norm (rightTubeCoreNormalComplex p)
  have habs : |1 - ‖rightTubeCorePlanarComplex p‖| ≤ (1 / 4 : ℝ) := by
    simpa [rightTubeCoreNormalComplex] using hre.trans hn
  rw [abs_le] at habs
  constructor <;> linarith

theorem rightTubeCoreInterpolatedNormalRadiusBound
    (m : C(RightTubeMinusLeftCore, Circle))
    (tp : unitInterval × RightTubeMinusLeftCore) :
    ‖rightTubeCoreNormalInterpolation m tp‖ ≤ (1 / 4 : ℝ) := by
  have ht0 : 0 ≤ (tp.1 : ℝ) := tp.1.2.1
  have ht1 : (tp.1 : ℝ) ≤ 1 := tp.1.2.2
  have hmer : ‖rightTubeCoreNormalComplex
      (apm_t02a03_circleMeridian (m tp.2))‖ ≤ (1 / 4 : ℝ) := by
    rw [norm_rightTubeCoreNormalComplex_circleMeridian]
    norm_num
  have hin : ‖rightTubeCoreNormalComplex tp.2.1‖ ≤ (1 / 4 : ℝ) :=
    rightTubeCoreInputNormalRadiusBound tp.2.1 tp.2.2.1
  have hleft : ‖(((1 - (tp.1 : ℝ) : ℝ) : ℂ))‖ = 1 - (tp.1 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
  have hright : ‖(((tp.1 : ℝ) : ℂ))‖ = (tp.1 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  rw [show rightTubeCoreNormalInterpolation m tp =
      ((1 - (tp.1 : ℝ) : ℝ) : ℂ) * rightTubeCoreNormalComplex
          (apm_t02a03_circleMeridian (m tp.2)) +
        ((tp.1 : ℝ) : ℂ) * rightTubeCoreNormalComplex tp.2.1 by
      rfl]
  calc
    _ ≤ ‖(((1 - (tp.1 : ℝ) : ℝ) : ℂ) * rightTubeCoreNormalComplex
          (apm_t02a03_circleMeridian (m tp.2)))‖ +
        ‖(((tp.1 : ℝ) : ℂ) * rightTubeCoreNormalComplex tp.2.1)‖ :=
      norm_add_le _ _
    _ = (1 - (tp.1 : ℝ)) * ‖rightTubeCoreNormalComplex
          (apm_t02a03_circleMeridian (m tp.2))‖ +
        (tp.1 : ℝ) * ‖rightTubeCoreNormalComplex tp.2.1‖ := by
      rw [norm_mul, norm_mul, hleft, hright]
    _ ≤ (1 - (tp.1 : ℝ)) * (1 / 4 : ℝ) +
        (tp.1 : ℝ) * (1 / 4 : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmer (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hin ht0)
    _ = (1 / 4 : ℝ) := by ring

theorem normalizedRightCorePlanar_circleMeridian
    (z : Circle) :
    NormedSpace.normalize (rightTubeCorePlanarComplex
      (apm_t02a03_circleMeridian z)) = (1 : ℂ) := by
  have habs : |(z : ℂ).re| ≤ 1 := by
    simpa [Circle.norm_coe z] using (RCLike.abs_re_le_norm (z : ℂ))
  have hpos : 0 < 1 - (1 / 8 : ℝ) * (z : ℂ).re := by
    have hhi : (z : ℂ).re ≤ 1 := (abs_le.mp habs).2
    norm_num at hhi ⊢
    linarith
  rw [show rightTubeCorePlanarComplex (apm_t02a03_circleMeridian z) =
      ((1 - (1 / 8 : ℝ) * (z : ℂ).re : ℝ) : ℂ) by
    apply Complex.ext <;>
      simp [rightTubeCorePlanarComplex, apm_t02a03_circleMeridian]]
  rw [show ((1 - (1 / 8 : ℝ) * (z : ℂ).re : ℝ) : ℂ) =
      (1 - (1 / 8 : ℝ) * (z : ℂ).re) • (1 : ℂ) by
    simp]
  exact (NormedSpace.normalize_smul_of_pos hpos (1 : ℂ)).trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (by norm_num))

theorem rightCorePolarReconstruction_circleMeridian
    (z : Circle) :
    rightTubeCorePolarReconstruction (1 : Circle)
      (rightTubeCoreNormalComplex (apm_t02a03_circleMeridian z)) =
      apm_t02a03_circleMeridian z := by
  ext i
  fin_cases i <;>
    simp [rightTubeCorePolarReconstruction, rightTubeCoreNormalComplex,
      rightTubeCorePlanarComplex, apm_t02a03_circleMeridian,
      Complex.norm_def, Complex.normSq_apply]
  have habs : |(z : ℂ).re| ≤ 1 := by
    simpa [Circle.norm_coe z] using (RCLike.abs_re_le_norm (z : ℂ))
  have hpos : 0 ≤ 1 - (8⁻¹ : ℝ) * (z : ℂ).re := by
    have hhi : (z : ℂ).re ≤ 1 := (abs_le.mp habs).2
    norm_num at hhi ⊢
    linarith
  rw [show (1 - 8⁻¹ * (z : ℂ).re) *
      (1 - 8⁻¹ * (z : ℂ).re) =
      (1 - 8⁻¹ * (z : ℂ).re) ^ 2 by ring]
  rw [Real.sqrt_sq hpos]
  ring

theorem rightTubeRadialCoefficient_pos
    (t : unitInterval) (n : ℂ) (hn : n ≠ 0) :
    0 < (1 - (t : ℝ)) * (1 / 8 : ℝ) + (t : ℝ) * ‖n‖ := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
  by_cases ht : (t : ℝ) = 1
  · rw [ht]
    simpa using hnpos
  · have hleft : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne ht1 ht)
    have hfirst : 0 < (1 - (t : ℝ)) * (1 / 8 : ℝ) :=
      mul_pos hleft (by norm_num)
    have hsecond : 0 ≤ (t : ℝ) * ‖n‖ :=
      mul_nonneg ht0 (norm_nonneg n)
    exact add_pos_of_pos_of_nonneg hfirst hsecond

noncomputable def rightTubeRadialNormalInterpolation
    (n : C(RightTubeMinusLeftCore, ℂ))
    (m : C(RightTubeMinusLeftCore, Circle)) :
    C(unitInterval × RightTubeMinusLeftCore, ℂ) where
  toFun tp := (((1 - (tp.1 : ℝ)) * (1 / 8 : ℝ) +
    (tp.1 : ℝ) * ‖n tp.2‖ : ℝ) : ℂ) * (m tp.2 : ℂ)
  continuous_toFun := by fun_prop

theorem rightTubeRadialNormalInterpolation_exists
    (n : C(RightTubeMinusLeftCore, ℂ))
    (m : C(RightTubeMinusLeftCore, Circle))
    (hm : ∀ p, (m p : ℂ) = NormedSpace.normalize (n p))
    (hn : ∀ p, n p ≠ 0) :
    ∃ N : C(unitInterval × RightTubeMinusLeftCore, ℂ),
      (∀ p, N (0, p) = ((1 / 8 : ℝ) : ℂ) * (m p : ℂ)) ∧
      (∀ p, N (1, p) = n p) ∧
      (∀ tp, N tp ≠ 0) := by
  refine ⟨rightTubeRadialNormalInterpolation n m, ?_, ?_, ?_⟩
  · intro p
    simp [rightTubeRadialNormalInterpolation]
  · intro p
    norm_num [rightTubeRadialNormalInterpolation]
    rw [hm]
    change ‖n p‖ • NormedSpace.normalize (n p) = n p
    exact NormedSpace.norm_smul_normalize (n p)
  · intro tp
    change (((1 - (tp.1 : ℝ)) * (1 / 8 : ℝ) +
      (tp.1 : ℝ) * ‖n tp.2‖ : ℝ) : ℂ) * (m tp.2 : ℂ) ≠ 0
    apply mul_ne_zero
    · exact_mod_cast (rightTubeRadialCoefficient_pos tp.1 (n tp.2) (hn tp.2)).ne'
    · exact Circle.coe_ne_zero (m tp.2)

noncomputable def rightTubeNormalCoordinate :
    C(RightTubeMinusLeftCore, ℂ) where
  toFun p := rightTubeNormalComplex p.1
  continuous_toFun :=
    continuous_rightTubeNormalComplex.comp continuous_subtype_val

theorem specializedRightTubeRadialNormalInterpolation_exists :
    ∃ N : C(unitInterval × RightTubeMinusLeftCore, ℂ),
      (∀ p, N (0, p) = ((1 / 8 : ℝ) : ℂ) *
        (rightTubeMeridianCoordinate p : ℂ)) ∧
      (∀ p, N (1, p) = rightTubeNormalComplex p.1) ∧
      (∀ tp, N tp ≠ 0) := by
  apply rightTubeRadialNormalInterpolation_exists
      rightTubeNormalCoordinate rightTubeMeridianCoordinate
  · intro p
    rfl
  · intro p hp
    exact p.2.2 ((rightTubeNormalComplex_eq_zero_iff p.1).mp hp)

noncomputable def rightTubeRadialAmbientDeformation :
    C(unitInterval × RightTubeMinusLeftCore, apm_t02a03_E3) where
  toFun tp := rightTubePolarReconstruction (rightTubePlanarRotation tp)
    (rightTubeRadialNormalInterpolation rightTubeNormalCoordinate
      rightTubeMeridianCoordinate tp)
  continuous_toFun := by
    have hR : Continuous (fun tp : unitInterval × RightTubeMinusLeftCore =>
        (rightTubePlanarRotation tp : ℂ)) :=
      (ContinuousMap.continuous rightTubePlanarRotation).subtype_val
    have hN : Continuous (fun tp : unitInterval × RightTubeMinusLeftCore =>
        rightTubeRadialNormalInterpolation rightTubeNormalCoordinate
          rightTubeMeridianCoordinate tp) :=
      ContinuousMap.continuous _
    unfold rightTubePolarReconstruction
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.add
        ((continuous_const.add (Complex.continuous_re.comp hN)).mul
          (Complex.continuous_re.comp hR))
    · exact (continuous_const.add (Complex.continuous_re.comp hN)).mul
        (Complex.continuous_im.comp hR)
    · exact Complex.continuous_im.comp hN

theorem rightTubeRadialAmbientDeformation_endpoints :
    (∀ p, rightTubeRadialAmbientDeformation (0, p) =
      apm_t02a03_circleMeridian (rightTubeMeridianCoordinate p)) ∧
    (∀ p, rightTubeRadialAmbientDeformation (1, p) = p.1) := by
  constructor
  · intro p
    ext i
    fin_cases i <;>
      simp [rightTubeRadialAmbientDeformation, rightTubePolarReconstruction,
        rightTubeRadialNormalInterpolation, rightTubePlanarRotation_zero,
        apm_t02a03_circleMeridian]
  · intro p
    change rightTubePolarReconstruction (rightTubePlanarRotation (1, p))
      (rightTubeRadialNormalInterpolation rightTubeNormalCoordinate
        rightTubeMeridianCoordinate (1, p)) = p.1
    rw [show rightTubeRadialNormalInterpolation rightTubeNormalCoordinate
        rightTubeMeridianCoordinate (1, p) = rightTubeNormalComplex p.1 by
      norm_num [rightTubeRadialNormalInterpolation, rightTubeNormalCoordinate]
      change ‖rightTubeNormalComplex p.1‖ •
          NormedSpace.normalize (rightTubeNormalComplex p.1) =
        rightTubeNormalComplex p.1
      exact NormedSpace.norm_smul_normalize _]
    have hrot : rightTubePlanarRotation (1, p) =
        ⟨NormedSpace.normalize (rightTubePlanarComplex p.1),
          mem_sphere_zero_iff_norm.mpr
            (NormedSpace.norm_normalize
              (rightTubePlanarComplex_ne_zero p.1 p.2.1))⟩ := by
      apply Subtype.ext
      exact rightTubePlanarRotation_one p
    rw [hrot]
    apply rightTubePolarReconstruction_self
    exact p.2.1

theorem positiveReconstructionRadius_rightTubeRadialNormalInterpolation
    (tp : unitInterval × RightTubeMinusLeftCore) :
    0 < 1 + (rightTubeRadialNormalInterpolation rightTubeNormalCoordinate
      rightTubeMeridianCoordinate tp).re := by
  let t : ℝ := tp.1
  let p : RightTubeMinusLeftCore := tp.2
  let n : ℂ := rightTubeNormalComplex p.1
  let m : ℂ := rightTubeMeridianCoordinate p
  have ht0 : 0 ≤ t := tp.1.2.1
  have ht1 : t ≤ 1 := tp.1.2.2
  have hmnorm : ‖m‖ = 1 := Circle.norm_coe (rightTubeMeridianCoordinate p)
  have hmre : -1 ≤ m.re := by
    have h := RCLike.abs_re_le_norm m
    rw [hmnorm] at h
    exact (abs_le.mp h).1
  have hn0 : n ≠ 0 := by
    intro hn
    exact p.2.2 ((rightTubeNormalComplex_eq_zero_iff p.1).mp hn)
  have hscale := NormedSpace.norm_smul_normalize n
  have hmn : ‖n‖ * m.re = n.re := by
    have h := congrArg Complex.re hscale
    have h' : ‖n‖ * (NormedSpace.normalize n).re = n.re :=
      (RCLike.smul_re ‖n‖ (NormedSpace.normalize n)).symm.trans h
    simpa [m, n, rightTubeMeridianCoordinate] using h'
  have hplanar : 0 < 1 + n.re := by
    have hp := norm_pos_iff.mpr (rightTubePlanarComplex_ne_zero p.1 p.2.1)
    simpa [n, rightTubeNormalComplex, rightTubePlanarComplex] using hp
  change 0 < 1 + (((((1 - t) * (1 / 8 : ℝ) + t * ‖n‖ : ℝ) : ℂ) * m).re)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hfirst : 0 < 1 + (1 / 8 : ℝ) * m.re := by nlinarith
  rw [show 1 + ((1 - t) * (1 / 8 : ℝ) + t * ‖n‖) * m.re =
      (1 - t) * (1 + (1 / 8 : ℝ) * m.re) + t * (1 + n.re) by
    rw [← hmn]
    ring]
  by_cases ht : t = 1
  · rw [ht]
    simpa using hplanar
  · have hleft : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 ht)
    exact add_pos_of_pos_of_nonneg (mul_pos hleft hfirst)
      (mul_nonneg ht0 hplanar.le)

theorem recoveredNormal_rightTubeRadialAmbientDeformation
    (tp : unitInterval × RightTubeMinusLeftCore) :
    rightTubeNormalComplex (rightTubeRadialAmbientDeformation tp) =
      rightTubeRadialNormalInterpolation rightTubeNormalCoordinate
        rightTubeMeridianCoordinate tp := by
  let n : ℂ := rightTubeRadialNormalInterpolation rightTubeNormalCoordinate
    rightTubeMeridianCoordinate tp
  let u : Circle := rightTubePlanarRotation tp
  have hpos : 0 < 1 + n.re := by
    simpa [n] using
      positiveReconstructionRadius_rightTubeRadialNormalInterpolation tp
  have hunorm : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  have hplanar : ‖(((1 + n.re : ℝ) : ℂ) * (u : ℂ))‖ = 1 + n.re := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, hunorm,
      mul_one]
  change rightTubeNormalComplex (rightTubePolarReconstruction u n) = n
  have hpcomplex :
      ((((rightTubePolarReconstruction u n) 0 + 1 : ℝ) : ℂ) +
        (((rightTubePolarReconstruction u n) 1 : ℝ) : ℂ) * Complex.I) =
      (((1 + n.re : ℝ) : ℂ) * (u : ℂ)) := by
    apply Complex.ext <;> simp [rightTubePolarReconstruction]
  unfold rightTubeNormalComplex
  rw [hpcomplex, hplanar]
  apply Complex.ext
  · simp
  · simp [rightTubePolarReconstruction]

theorem avoidsLeftCore_rightTubeRadialAmbientDeformation
    (tp : unitInterval × RightTubeMinusLeftCore) :
    rightTubeRadialAmbientDeformation tp ∉ Set.range apm_t02a03_leftCore := by
  intro hmem
  have hz : rightTubeNormalComplex (rightTubeRadialAmbientDeformation tp) = 0 :=
    (rightTubeNormalComplex_eq_zero_iff _).mpr hmem
  rw [recoveredNormal_rightTubeRadialAmbientDeformation] at hz
  have hn : rightTubeNormalCoordinate tp.2 ≠ 0 := by
    intro h
    exact tp.2.2.2 ((rightTubeNormalComplex_eq_zero_iff tp.2.1).mp h)
  have hne : rightTubeRadialNormalInterpolation rightTubeNormalCoordinate
      rightTubeMeridianCoordinate tp ≠ 0 := by
    change (((1 - (tp.1 : ℝ)) * (1 / 8 : ℝ) +
      (tp.1 : ℝ) * ‖rightTubeNormalCoordinate tp.2‖ : ℝ) : ℂ) *
        (rightTubeMeridianCoordinate tp.2 : ℂ) ≠ 0
    exact mul_ne_zero
      (by exact_mod_cast (rightTubeRadialCoefficient_pos tp.1
        (rightTubeNormalCoordinate tp.2) hn).ne')
      (Circle.coe_ne_zero (rightTubeMeridianCoordinate tp.2))
  exact hne hz

theorem reconstructionMemRightTube_rightTubeCorePolar
    (u : Circle) (n : Complex) (hn : ‖n‖ ≤ (1 / 4 : Real)) :
    rightTubeCorePolarReconstruction u n ∈ apm_t02a03_rightTube := by
  rw [apm_t02a03_rightTube,
    isCompact_range_rightCore.cthickening_eq_biUnion_closedBall (by norm_num)]
  simp only [Set.mem_iUnion, Metric.mem_closedBall]
  refine ⟨rightCoreCircle u, ?_, ?_⟩
  · rw [← range_rightCoreCircle]
    exact ⟨u, rfl⟩
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    have hu : (u : Complex).re * (u : Complex).re +
        (u : Complex).im * (u : Complex).im = 1 := by
      have h := Complex.sq_norm (u : Complex)
      rw [Circle.norm_coe] at h
      simpa [Complex.normSq_apply, pow_two] using h.symm
    simp [rightTubeCorePolarReconstruction, rightCoreCircle, Fin.sum_univ_succ]
    rw [show
        ((u : Complex).re - (1 - n.re) * (u : Complex).re) ^ 2 +
          (((1 - n.re) * (u : Complex).im - (u : Complex).im) ^ 2 + n.im ^ 2) =
        n.re ^ 2 + n.im ^ 2 by nlinarith]
    simpa [Complex.norm_def, Complex.normSq_apply, pow_two] using hn

theorem rightTubeCoreRadialAmbientDeformation_exists :
    ∃ H : C(unitInterval × RightTubeMinusLeftCore, apm_t02a03_E3),
      (∀ p, H (0, p) = rightTubeCorePolarReconstruction
        (rightTubeCoreAngularCoordinate p)
        (rightTubeCoreNormalComplex
          (apm_t02a03_circleMeridian (rightTubeMeridianCoordinate p)))) ∧
      (∀ p, H (1, p) = p.1) ∧
      (∀ tp, H tp ∈ apm_t02a03_rightTube) := by
  let H : C(unitInterval × RightTubeMinusLeftCore, apm_t02a03_E3) :=
    ⟨fun tp => rightTubeCorePolarReconstruction
        (rightTubeCoreAngularCoordinate tp.2)
        (rightTubeCoreNormalInterpolation rightTubeMeridianCoordinate tp), by
      have hu : Continuous (fun tp : unitInterval × RightTubeMinusLeftCore =>
          rightTubeCoreAngularCoordinate tp.2) :=
        (ContinuousMap.continuous rightTubeCoreAngularCoordinate).comp continuous_snd
      have hn : Continuous (fun tp : unitInterval × RightTubeMinusLeftCore =>
          rightTubeCoreNormalInterpolation rightTubeMeridianCoordinate tp) :=
        ContinuousMap.continuous _
      exact rightTubeCoreTubularCoordinates_continuous.2.comp (hu.prodMk hn)⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro p
    simp [H, rightTubeCoreNormalInterpolation_zero]
  · intro p
    simp only [H, ContinuousMap.coe_mk, rightTubeCoreNormalInterpolation_one]
    apply rightTubeCorePolarReconstruction_self
    exact p.2.1
  · intro tp
    apply reconstructionMemRightTube_rightTubeCorePolar
    exact rightTubeCoreInterpolatedNormalRadiusBound rightTubeMeridianCoordinate tp

theorem reconstructionAvoidsLeftCore_rightTubeCorePolar_of_im_ne_zero
    (u : Circle) (n : Complex) (hn : n.im ≠ 0) :
    rightTubeCorePolarReconstruction u n ∉ Set.range apm_t02a03_leftCore := by
  rintro ⟨t, ht⟩
  have hcoord := congrArg (fun p : apm_t02a03_E3 => p 2) ht
  simp [rightTubeCorePolarReconstruction, apm_t02a03_leftCore] at hcoord
  exact hn hcoord.symm

theorem corePolar_leftCore_collision_equation
    (u : Circle) (n : Complex)
    (hmem : rightTubeCorePolarReconstruction u n ∈
      Set.range apm_t02a03_leftCore) :
    (1 - n.re) ^ 2 - 4 * (1 - n.re) * (u : Complex).re + 3 = 0 := by
  obtain ⟨t, ht⟩ := hmem
  have hx := congrArg (fun p : apm_t02a03_E3 => p 0) ht
  have hy := congrArg (fun p : apm_t02a03_E3 => p 1) ht
  simp [rightTubeCorePolarReconstruction, apm_t02a03_leftCore] at hx hy
  have hu : (u : Complex).re ^ 2 + (u : Complex).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe u
  have htrig := Real.sin_sq_add_cos_sq t
  rw [show Real.cos t = 2 - (1 - n.re) * (u : Complex).re by linarith,
    show Real.sin t = (1 - n.re) * (u : Complex).im by linarith] at htrig
  nlinarith

theorem collisionPolynomial_ne_implies_avoidsLeftCore_rightTubeCorePolar
    (u : Circle) (n : Complex)
    (hpoly : (1 - n.re) ^ 2 - 4 * (1 - n.re) * (u : Complex).re + 3 ≠ 0) :
    rightTubeCorePolarReconstruction u n ∉ Set.range apm_t02a03_leftCore := by
  intro hmem
  exact hpoly (corePolar_leftCore_collision_equation u n hmem)

theorem collisionPolynomial_pos_of_normal_re_pos
    (u : Circle) (n : Complex)
    (hnorm : ‖n‖ ≤ (1 / 4 : Real)) (hre : 0 < n.re) :
    0 < (1 - n.re) ^ 2 - 4 * (1 - n.re) * (u : Complex).re + 3 := by
  have hnre : n.re ≤ ‖n‖ := RCLike.re_le_norm n
  have hrpos : 0 < 1 - n.re := by
    linarith
  have hrlt : 1 - n.re < 1 := by linarith
  have hua : (u : Complex).re ≤ 1 := by
    simpa [Circle.norm_coe u] using RCLike.re_le_norm (u : Complex)
  have hmul : (1 - n.re) * (u : Complex).re ≤ 1 - n.re :=
    by simpa using mul_le_mul_of_nonneg_left hua hrpos.le
  nlinarith [sq_nonneg ((1 - n.re) - 2)]

theorem nonpositiveNormalSafeCorridor_collisionPolynomial_pos
    (u : Circle) (n : Complex)
    (hnorm : ‖n‖ ≤ (1 / 4 : Real)) (hnre : n.re ≤ 0)
    (hure : (u : Complex).re ≤ (9 / 10 : Real)) :
    0 < (1 - n.re) ^ 2 - 4 * (1 - n.re) * (u : Complex).re + 3 := by
  have habs : |n.re| ≤ ‖n‖ := RCLike.abs_re_le_norm n
  have hnlo : -(1 / 4 : Real) ≤ n.re :=
    (abs_le.mp (habs.trans hnorm)).1
  have hrpos : 0 ≤ 1 - n.re := by linarith
  have hmul : (1 - n.re) * (u : Complex).re ≤
      (1 - n.re) * (9 / 10 : Real) :=
    mul_le_mul_of_nonneg_left hure hrpos
  nlinarith [sq_nonneg (n.re + 1 / 4)]

theorem zeroHeightCollisionPolynomial_eq_zero_implies_leftCore
    (u : Circle) (n : Complex) (him : n.im = 0)
    (hpoly : (1 - n.re) ^ 2 -
      4 * (1 - n.re) * (u : Complex).re + 3 = 0) :
    rightTubeCorePolarReconstruction u n ∈ Set.range apm_t02a03_leftCore := by
  let w : Complex :=
    ((2 - (1 - n.re) * (u : Complex).re : Real) : Complex) +
      (((1 - n.re) * (u : Complex).im : Real) : Complex) * Complex.I
  have hu : (u : Complex).re ^ 2 + (u : Complex).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe u
  have hwsq : Complex.normSq w = 1 := by
    simp [w, Complex.normSq_apply]
    nlinarith
  have hwnorm : ‖w‖ = 1 := by
    rw [Complex.norm_def, hwsq]
    norm_num
  have hw0 : w ≠ 0 := by
    intro hw
    simp [hw] at hwnorm
  refine ⟨Complex.arg w, ?_⟩
  ext i
  fin_cases i
  · have hc := Complex.cos_arg hw0
    rw [hwnorm, div_one] at hc
    change -1 + Real.cos (Complex.arg w) =
      1 - (1 - n.re) * (u : Complex).re
    rw [hc]
    simp [w]
    ring
  · have hs := Complex.sin_arg w
    rw [hwnorm, div_one] at hs
    simpa [rightTubeCorePolarReconstruction, apm_t02a03_leftCore, w] using hs
  · simp [rightTubeCorePolarReconstruction, apm_t02a03_leftCore, him]

theorem inputZeroHeight_collisionPolynomial_ne
    (p : RightTubeMinusLeftCore)
    (him : (rightTubeCoreNormalComplex p.1).im = 0) :
    (1 - (rightTubeCoreNormalComplex p.1).re) ^ 2 -
      4 * (1 - (rightTubeCoreNormalComplex p.1).re) *
        (rightTubeCoreAngularCoordinate p : Complex).re + 3 ≠ 0 := by
  intro hpoly
  have hmem := zeroHeightCollisionPolynomial_eq_zero_implies_leftCore
    (rightTubeCoreAngularCoordinate p) (rightTubeCoreNormalComplex p.1)
    him hpoly
  have hself : rightTubeCorePolarReconstruction
      (rightTubeCoreAngularCoordinate p) (rightTubeCoreNormalComplex p.1) = p.1 := by
    simpa [rightTubeCoreAngularCoordinate] using
      rightTubeCorePolarReconstruction_self p.1 p.2.1
  rw [hself] at hmem
  exact p.2.2 hmem

theorem meridianStart_collisionPolynomial_factor
    (z : Circle) :
    let n := rightTubeCoreNormalComplex (apm_t02a03_circleMeridian z)
    (1 - n.re) ^ 2 - 4 * (1 - n.re) * ((1 : Circle) : Complex).re + 3 =
      ((z : Complex).re / 8) * (2 + (z : Complex).re / 8) := by
  dsimp
  have habs : |(z : Complex).re| ≤ 1 := by
    simpa [Circle.norm_coe z] using RCLike.abs_re_le_norm (z : Complex)
  have hpos : 0 ≤ 1 - (8⁻¹ : Real) * (z : Complex).re := by
    have hhi : (z : Complex).re ≤ 1 := (abs_le.mp habs).2
    linarith
  simp [rightTubeCoreNormalComplex, rightTubeCorePlanarComplex,
    apm_t02a03_circleMeridian, Complex.norm_def, Complex.normSq_apply]
  rw [show (1 - 8⁻¹ * (z : Complex).re) *
      (1 - 8⁻¹ * (z : Complex).re) =
      (1 - 8⁻¹ * (z : Complex).re) ^ 2 by ring]
  rw [Real.sqrt_sq hpos]
  ring

theorem inputCollisionPolynomial_factor_rightTubeNormalReal
    (p : RightTubeMinusLeftCore) :
    (1 - (rightTubeCoreNormalComplex p.1).re) ^ 2 -
      4 * (1 - (rightTubeCoreNormalComplex p.1).re) *
        (rightTubeCoreAngularCoordinate p : Complex).re + 3 =
      (rightTubeNormalComplex p.1).re *
        ((rightTubeNormalComplex p.1).re + 2) := by
  let v := rightTubeCorePlanarComplex p.1
  have hv0 : v ≠ 0 := rightTubeCorePlanarComplex_ne_zero p.1 p.2.1
  have hscale := NormedSpace.norm_smul_normalize v
  have hre : ‖v‖ * (NormedSpace.normalize v).re = v.re := by
    have h := congrArg Complex.re hscale
    exact (RCLike.smul_re ‖v‖ (NormedSpace.normalize v)).symm.trans h
  have hleft : ‖rightTubePlanarComplex p.1‖ ^ 2 =
      (rightTubePlanarComplex p.1).re ^ 2 +
        (rightTubePlanarComplex p.1).im ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using
      (Complex.sq_norm (rightTubePlanarComplex p.1))
  have hncore : (rightTubeCoreNormalComplex p.1).re = 1 - ‖v‖ := by
    simp [rightTubeCoreNormalComplex, v]
  have hang : (rightTubeCoreAngularCoordinate p : Complex).re =
      (NormedSpace.normalize v).re := by
    rfl
  have hnleft : (rightTubeNormalComplex p.1).re =
      ‖rightTubePlanarComplex p.1‖ - 1 := by
    simp [rightTubeNormalComplex, rightTubePlanarComplex]
  rw [hncore, hang, hnleft]
  ring_nf
  rw [hre]
  have hvre : v.re = 1 - p.1 0 := by
    simp [v, rightTubeCorePlanarComplex]
  have hvnorm : ‖v‖ ^ 2 = (1 - p.1 0) ^ 2 + (p.1 1) ^ 2 := by
    rw [Complex.sq_norm]
    simp [v, rightTubeCorePlanarComplex, Complex.normSq_apply]
    ring
  have hlre : (rightTubePlanarComplex p.1).re = p.1 0 + 1 := by
    simp [rightTubePlanarComplex]
  have hlim : (rightTubePlanarComplex p.1).im = p.1 1 := by
    simp [rightTubePlanarComplex]
  rw [hvre, hvnorm, hleft, hlre, hlim]
  ring

theorem inputCollisionPolynomial_positiveFactor_meridianReal
    (p : RightTubeMinusLeftCore) :
    ∃ c : ℝ, 0 < c ∧
      (1 - (rightTubeCoreNormalComplex p.1).re) ^ 2 -
          4 * (1 - (rightTubeCoreNormalComplex p.1).re) *
            (rightTubeCoreAngularCoordinate p : Complex).re + 3 =
        c * (rightTubeMeridianCoordinate p : Complex).re := by
  let n : ℂ := rightTubeNormalComplex p.1
  let m : ℂ := rightTubeMeridianCoordinate p
  have hn0 : n ≠ 0 := by
    intro hn
    exact p.2.2 ((rightTubeNormalComplex_eq_zero_iff p.1).mp hn)
  have hnorm : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  have hsecond : 0 < n.re + 2 := by
    simp [n, rightTubeNormalComplex]
    linarith [norm_nonneg
      (((p.1 0 : ℂ) + 1) + (p.1 1 : ℂ) * Complex.I)]
  have hscale := NormedSpace.norm_smul_normalize n
  have hmn : ‖n‖ * m.re = n.re := by
    have h := congrArg Complex.re hscale
    have h' : ‖n‖ * (NormedSpace.normalize n).re = n.re :=
      (RCLike.smul_re ‖n‖ (NormedSpace.normalize n)).symm.trans h
    simpa [m, n, rightTubeMeridianCoordinate] using h'
  refine ⟨‖n‖ * (n.re + 2), mul_pos hnorm hsecond, ?_⟩
  rw [inputCollisionPolynomial_factor_rightTubeNormalReal]
  change n.re * (n.re + 2) = (‖n‖ * (n.re + 2)) * m.re
  rw [← hmn]
  ring

theorem collisionEndpoint_positiveFactor_signBridge
    (p : RightTubeMinusLeftCore) :
    let m : ℂ := rightTubeMeridianCoordinate p
    let n₀ := rightTubeCoreNormalComplex
      (apm_t02a03_circleMeridian (rightTubeMeridianCoordinate p))
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ((1 - n₀.re) ^ 2 - 4 * (1 - n₀.re) *
          ((1 : Circle) : Complex).re + 3 = a * m.re) ∧
      ((1 - (rightTubeCoreNormalComplex p.1).re) ^ 2 -
          4 * (1 - (rightTubeCoreNormalComplex p.1).re) *
            (rightTubeCoreAngularCoordinate p : Complex).re + 3 = b * m.re) := by
  dsimp only
  let n : ℂ := rightTubeNormalComplex p.1
  have hn0 : n ≠ 0 := by
    intro hn
    exact p.2.2 ((rightTubeNormalComplex_eq_zero_iff p.1).mp hn)
  have hnorm : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  have hsecond : 0 < n.re + 2 := by
    simp [n, rightTubeNormalComplex]
    linarith [norm_nonneg
      (((p.1 0 : ℂ) + 1) + (p.1 1 : ℂ) * Complex.I)]
  let m : ℂ := rightTubeMeridianCoordinate p
  let b : ℝ := ‖n‖ * (n.re + 2)
  have hb : 0 < b := mul_pos hnorm hsecond
  have hscale := NormedSpace.norm_smul_normalize n
  have hmn : ‖n‖ * m.re = n.re := by
    have h := congrArg Complex.re hscale
    have h' : ‖n‖ * (NormedSpace.normalize n).re = n.re :=
      (RCLike.smul_re ‖n‖ (NormedSpace.normalize n)).symm.trans h
    simpa [m, n, rightTubeMeridianCoordinate] using h'
  have hend :
      (1 - (rightTubeCoreNormalComplex p.1).re) ^ 2 -
          4 * (1 - (rightTubeCoreNormalComplex p.1).re) *
            (rightTubeCoreAngularCoordinate p : Complex).re + 3 = b * m.re := by
    rw [inputCollisionPolynomial_factor_rightTubeNormalReal]
    change n.re * (n.re + 2) = (‖n‖ * (n.re + 2)) * m.re
    rw [← hmn]
    ring
  let a : ℝ := (1 / 8 : ℝ) * (2 + m.re / 8)
  have hmabs : |m.re| ≤ 1 := by
    simpa [m, Circle.norm_coe (rightTubeMeridianCoordinate p)] using
      RCLike.abs_re_le_norm m
  have ha : 0 < a := by
    have hmlo : -1 ≤ m.re := (abs_le.mp hmabs).1
    dsimp [a]
    have hfactor : 0 < 2 + m.re / 8 := by linarith
    exact mul_pos (by norm_num) hfactor
  refine ⟨a, b, ha, hb, ?_, hend⟩
  rw [meridianStart_collisionPolynomial_factor]
  change m.re / 8 * (2 + m.re / 8) = a * m.re
  dsimp [a]
  ring

theorem rightTubeMeridianCoordinate_im_positiveFactor_height
    (p : RightTubeMinusLeftCore) :
    ∃ c : ℝ, 0 < c ∧
      (rightTubeMeridianCoordinate p : Complex).im = c * p.1 2 := by
  let n : ℂ := rightTubeNormalComplex p.1
  have hn0 : n ≠ 0 := by
    intro hn
    exact p.2.2 ((rightTubeNormalComplex_eq_zero_iff p.1).mp hn)
  have hnorm : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  refine ⟨(‖n‖)⁻¹, inv_pos.mpr hnorm, ?_⟩
  have hscale := NormedSpace.norm_smul_normalize n
  have him : ‖n‖ * (NormedSpace.normalize n).im = n.im := by
    have h := congrArg Complex.im hscale
    exact (RCLike.smul_im ‖n‖ (NormedSpace.normalize n)).symm.trans h
  have hn_im : n.im = p.1 2 := by
    simp [n, rightTubeNormalComplex]
  change (NormedSpace.normalize n).im = ‖n‖⁻¹ * p.1 2
  rw [← hn_im]
  rw [← him]
  field_simp

theorem nonzeroHeight_im_ne_zero_rightTubeCoreNormalInterpolation
    (tp : unitInterval × RightTubeMinusLeftCore)
    (hheight : tp.2.1 2 ≠ 0) :
    (rightTubeCoreNormalInterpolation rightTubeMeridianCoordinate tp).im ≠ 0 := by
  let t : ℝ := tp.1
  let p : RightTubeMinusLeftCore := tp.2
  obtain ⟨c, hc, hm⟩ :=
    rightTubeMeridianCoordinate_im_positiveFactor_height p
  have ht0 : 0 ≤ t := tp.1.2.1
  have ht1 : t ≤ 1 := tp.1.2.2
  have hcoeff : 0 < (1 - t) * (c / 8) + t := by
    by_cases ht : t = 1
    · rw [ht]
      norm_num
    · have hlt : t < 1 := lt_of_le_of_ne ht1 ht
      have hleft : 0 < (1 - t) * (c / 8) :=
        mul_pos (sub_pos.mpr hlt) (div_pos hc (by norm_num))
      exact add_pos_of_pos_of_nonneg hleft ht0
  have him :
      (rightTubeCoreNormalInterpolation rightTubeMeridianCoordinate tp).im =
        ((1 - t) * (c / 8) + t) * p.1 2 := by
    simp [rightTubeCoreNormalInterpolation, rightTubeCoreNormalComplex,
      apm_t02a03_circleMeridian, t, p]
    rw [hm]
    ring
  rw [him]
  exact mul_ne_zero hcoeff.ne' hheight

theorem nonzeroHeight_avoidsLeftCore_rightTubeCoreRadialAmbient
    (tp : unitInterval × RightTubeMinusLeftCore)
    (hheight : tp.2.1 2 ≠ 0) :
    rightTubeCorePolarReconstruction
        (rightTubeCoreAngularCoordinate tp.2)
        (rightTubeCoreNormalInterpolation rightTubeMeridianCoordinate tp) ∉
      Set.range apm_t02a03_leftCore := by
  apply reconstructionAvoidsLeftCore_rightTubeCorePolar_of_im_ne_zero
  exact nonzeroHeight_im_ne_zero_rightTubeCoreNormalInterpolation tp hheight

theorem zeroHeight_rightTubeMeridianCoordinate_re_sq
    (p : RightTubeMinusLeftCore) (hheight : p.1 2 = 0) :
    (rightTubeMeridianCoordinate p : Complex).re ^ 2 = 1 := by
  obtain ⟨c, hc, him⟩ :=
    rightTubeMeridianCoordinate_im_positiveFactor_height p
  have him0 : (rightTubeMeridianCoordinate p : Complex).im = 0 := by
    rw [him, hheight]
    ring
  have hnorm := Circle.normSq_coe (rightTubeMeridianCoordinate p)
  simpa only [Complex.normSq_apply, him0, zero_mul, add_zero, pow_two]
    using hnorm

theorem signCases_zeroHeight_rightTubeMeridianCoordinate_re
    (p : RightTubeMinusLeftCore) (hheight : p.1 2 = 0) :
    (rightTubeMeridianCoordinate p : Complex).re = 1 ∨
      (rightTubeMeridianCoordinate p : Complex).re = -1 := by
  have hs := zeroHeight_rightTubeMeridianCoordinate_re_sq p hheight
  rw [sq_eq_one_iff] at hs
  exact hs

theorem positiveSign_rightTubeNormalComplex_re_pos
    (p : RightTubeMinusLeftCore)
    (hm : (rightTubeMeridianCoordinate p : Complex).re = 1) :
    0 < (rightTubeNormalComplex p.1).re := by
  let n : Complex := rightTubeNormalComplex p.1
  have hn0 : n ≠ 0 := by
    intro hn
    exact p.2.2 ((rightTubeNormalComplex_eq_zero_iff p.1).mp hn)
  have hnorm : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  have hscale := NormedSpace.norm_smul_normalize n
  have hre : ‖n‖ * (NormedSpace.normalize n).re = n.re := by
    have h := congrArg Complex.re hscale
    exact (RCLike.smul_re ‖n‖ (NormedSpace.normalize n)).symm.trans h
  have hm' : (NormedSpace.normalize n).re = 1 := by
    simpa [n, rightTubeMeridianCoordinate] using hm
  rw [hm'] at hre
  simp only [mul_one] at hre
  change 0 < n.re
  rw [← hre]
  exact hnorm

theorem positiveSign_radialStart_collisionPolynomial_pos
    (p : RightTubeMinusLeftCore)
    (hm : (rightTubeMeridianCoordinate p : Complex).re = 1) :
    let n := rightTubeCoreNormalComplex
      (apm_t02a03_circleMeridian (rightTubeMeridianCoordinate p))
    0 < (1 - n.re) ^ 2 - 4 * (1 - n.re) *
      (rightTubeCoreAngularCoordinate p : Complex).re + 3 := by
  dsimp only
  apply collisionPolynomial_pos_of_normal_re_pos
  · rw [norm_rightTubeCoreNormalComplex_circleMeridian]
    norm_num
  · simp [rightTubeCoreNormalComplex, rightTubeCorePlanarComplex,
      apm_t02a03_circleMeridian, hm]
    norm_num [Real.norm_eq_abs]

theorem positiveSign_input_collisionPolynomial_pos
    (p : RightTubeMinusLeftCore)
    (hm : (rightTubeMeridianCoordinate p : Complex).re = 1) :
    0 < (1 - (rightTubeCoreNormalComplex p.1).re) ^ 2 -
      4 * (1 - (rightTubeCoreNormalComplex p.1).re) *
        (rightTubeCoreAngularCoordinate p : Complex).re + 3 := by
  obtain ⟨c, hc, hpoly⟩ :=
    inputCollisionPolynomial_positiveFactor_meridianReal p
  rw [hpoly, hm, mul_one]
  exact hc

theorem realEndpoints_zeroHeight_rightTubeCoreNormals
    (p : RightTubeMinusLeftCore) (hheight : p.1 2 = 0) :
    (rightTubeCoreNormalComplex
          (apm_t02a03_circleMeridian (rightTubeMeridianCoordinate p))).im = 0 ∧
      (rightTubeCoreNormalComplex p.1).im = 0 := by
  constructor
  · obtain ⟨c, hc, him⟩ :=
      rightTubeMeridianCoordinate_im_positiveFactor_height p
    simp [rightTubeCoreNormalComplex, apm_t02a03_circleMeridian, him, hheight]
  · simp [rightTubeCoreNormalComplex, hheight]

noncomputable def zeroHeightSignedImaginaryWaypoint
    (p : RightTubeMinusLeftCore) : ℂ :=
  (((1 / 8 : ℝ) * (rightTubeMeridianCoordinate p : ℂ).re : ℝ) : ℂ) * Complex.I

theorem zeroHeight_signedImaginaryWaypoint_properties
    (p : RightTubeMinusLeftCore) (hheight : p.1 2 = 0) :
    ‖zeroHeightSignedImaginaryWaypoint p‖ = (1 / 8 : ℝ) ∧
      (zeroHeightSignedImaginaryWaypoint p).im ≠ 0 := by
  obtain ⟨c, hc, him⟩ :=
    rightTubeMeridianCoordinate_im_positiveFactor_height p
  have him0 : (rightTubeMeridianCoordinate p : ℂ).im = 0 := by
    rw [him, hheight]
    ring
  have hs : (rightTubeMeridianCoordinate p : ℂ).re ^ 2 = 1 := by
    have hnorm := Circle.normSq_coe (rightTubeMeridianCoordinate p)
    simpa only [Complex.normSq_apply, him0, zero_mul, add_zero, pow_two]
      using hnorm
  rcases (sq_eq_one_iff.mp hs) with hm | hm
  · simp [zeroHeightSignedImaginaryWaypoint, hm, Complex.norm_def]
  · simp [zeroHeightSignedImaginaryWaypoint, hm, Complex.norm_def]

noncomputable def coreNormalAffineLeg
    (t : unitInterval) (n w : ℂ) : ℂ :=
  ((1 - (t : ℝ) : ℝ) : ℂ) * n + ((t : ℝ) : ℂ) * w

theorem coreNormalAffineLeg_radius_and_im_ne_zero
    (t : unitInterval) (n w : ℂ)
    (hnim : n.im = 0) (hwim : w.im ≠ 0) (ht : (t : ℝ) ≠ 0)
    (hnorm : ‖n‖ ≤ (1 / 4 : ℝ)) (hwnorm : ‖w‖ ≤ (1 / 4 : ℝ)) :
    ‖coreNormalAffineLeg t n w‖ ≤ (1 / 4 : ℝ) ∧
      (coreNormalAffineLeg t n w).im ≠ 0 := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  constructor
  · calc
      ‖coreNormalAffineLeg t n w‖
          ≤ ‖((1 - (t : ℝ) : ℝ) : ℂ) * n‖ +
              ‖((t : ℝ) : ℂ) * w‖ := norm_add_le _ _
      _ = (1 - (t : ℝ)) * ‖n‖ + (t : ℝ) * ‖w‖ := by
        rw [norm_mul, norm_mul]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0,
          abs_of_nonneg (sub_nonneg.mpr ht1)]
      _ ≤ (1 / 4 : ℝ) := by nlinarith
  · simp only [coreNormalAffineLeg, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hnim,
      mul_zero, zero_add]
    exact mul_ne_zero ht hwim

theorem zeroHeight_specializedCoreNormalAffineLegs_radius_and_im_ne_zero
    (p : RightTubeMinusLeftCore) (hheight : p.1 2 = 0)
    (t : unitInterval) (ht : (t : ℝ) ≠ 0) :
    let n₀ := rightTubeCoreNormalComplex
      (apm_t02a03_circleMeridian (rightTubeMeridianCoordinate p))
    let n₁ := rightTubeCoreNormalComplex p.1
    let w := zeroHeightSignedImaginaryWaypoint p
    (‖coreNormalAffineLeg t n₀ w‖ ≤ (1 / 4 : ℝ) ∧
        (coreNormalAffineLeg t n₀ w).im ≠ 0) ∧
      (‖coreNormalAffineLeg t n₁ w‖ ≤ (1 / 4 : ℝ) ∧
        (coreNormalAffineLeg t n₁ w).im ≠ 0) := by
  dsimp only
  obtain ⟨hn0im, hn1im⟩ :=
    realEndpoints_zeroHeight_rightTubeCoreNormals p hheight
  obtain ⟨hwnorm, hwim⟩ :=
    zeroHeight_signedImaginaryWaypoint_properties p hheight
  have hwquarter : ‖zeroHeightSignedImaginaryWaypoint p‖ ≤ (1 / 4 : ℝ) := by
    rw [hwnorm]
    norm_num
  constructor
  · apply coreNormalAffineLeg_radius_and_im_ne_zero t _ _ hn0im hwim ht
    · rw [norm_rightTubeCoreNormalComplex_circleMeridian]
      norm_num
    · exact hwquarter
  · apply coreNormalAffineLeg_radius_and_im_ne_zero t _ _ hn1im hwim ht
    · exact rightTubeCoreInputNormalRadiusBound p.1 p.2.1
    · exact hwquarter

noncomputable def zeroHeightCoreNormalDetour
    (t : unitInterval) (p : RightTubeMinusLeftCore) : ℂ :=
  let n₀ := rightTubeCoreNormalComplex
    (apm_t02a03_circleMeridian (rightTubeMeridianCoordinate p))
  let n₁ := rightTubeCoreNormalComplex p.1
  let w := zeroHeightSignedImaginaryWaypoint p
  if (t : ℝ) ≤ 1 / 2 then
    ((1 - 2 * (t : ℝ) : ℝ) : ℂ) * n₀ + ((2 * (t : ℝ) : ℝ) : ℂ) * w
  else
    ((2 - 2 * (t : ℝ) : ℝ) : ℂ) * w + ((2 * (t : ℝ) - 1 : ℝ) : ℂ) * n₁

theorem zeroHeightCoreNormalDetour_endpoints_midpoint
    (p : RightTubeMinusLeftCore) :
    zeroHeightCoreNormalDetour 0 p = rightTubeCoreNormalComplex
        (apm_t02a03_circleMeridian (rightTubeMeridianCoordinate p)) ∧
      zeroHeightCoreNormalDetour 1 p = rightTubeCoreNormalComplex p.1 ∧
      zeroHeightCoreNormalDetour ⟨1 / 2, by constructor <;> norm_num⟩ p =
        zeroHeightSignedImaginaryWaypoint p := by
  norm_num [zeroHeightCoreNormalDetour]

theorem continuous_zeroHeightCoreNormalDetour :
    Continuous (fun tp : unitInterval × RightTubeMinusLeftCore =>
      zeroHeightCoreNormalDetour tp.1 tp.2) := by
  have hn := rightTubeCoreTubularCoordinates_continuous.1
  have hc : Continuous
      ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_circleMeridian := by
    unfold ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_circleMeridian
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hn₀ : Continuous (fun p : RightTubeMinusLeftCore =>
      rightTubeCoreNormalComplex
        (ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_circleMeridian
          (rightTubeMeridianCoordinate p))) :=
    hn.comp (hc.comp rightTubeMeridianCoordinate.continuous)
  have hn₁ : Continuous (fun p : RightTubeMinusLeftCore =>
      rightTubeCoreNormalComplex p.1) :=
    hn.comp continuous_subtype_val
  have hm : Continuous (fun p : RightTubeMinusLeftCore =>
      (rightTubeMeridianCoordinate p : ℂ).re) :=
    Complex.continuous_re.comp
      (continuous_subtype_val.comp rightTubeMeridianCoordinate.continuous)
  have hw : Continuous zeroHeightSignedImaginaryWaypoint := by
    unfold zeroHeightSignedImaginaryWaypoint
    fun_prop
  unfold zeroHeightCoreNormalDetour
  apply continuous_if_le
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro tp h
    simp only at h
    rw [h]
    norm_num

theorem zeroHeightCoreNormalDetour_radius_le
    (p : RightTubeMinusLeftCore) (hheight : p.1 2 = 0)
    (t : unitInterval) :
    ‖zeroHeightCoreNormalDetour t p‖ ≤ (1 / 4 : ℝ) := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  obtain ⟨hwnorm, hwim⟩ :=
    zeroHeight_signedImaginaryWaypoint_properties p hheight
  unfold zeroHeightCoreNormalDetour
  split_ifs with hhalf
  · have ha : 0 ≤ 1 - 2 * (t : ℝ) := by linarith
    have hb : 0 ≤ 2 * (t : ℝ) := by positivity
    calc
      ‖((1 - 2 * (t : ℝ) : ℝ) : ℂ) *
            rightTubeCoreNormalComplex
              (ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_circleMeridian
                (rightTubeMeridianCoordinate p)) +
          ((2 * (t : ℝ) : ℝ) : ℂ) * zeroHeightSignedImaginaryWaypoint p‖
          ≤ ‖((1 - 2 * (t : ℝ) : ℝ) : ℂ) *
                rightTubeCoreNormalComplex
                  (ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_circleMeridian
                    (rightTubeMeridianCoordinate p))‖ +
              ‖((2 * (t : ℝ) : ℝ) : ℂ) *
                zeroHeightSignedImaginaryWaypoint p‖ := norm_add_le _ _
      _ = (1 - 2 * (t : ℝ)) * (1 / 8 : ℝ) +
            (2 * (t : ℝ)) * (1 / 8 : ℝ) := by
        rw [norm_mul, norm_mul,
          norm_rightTubeCoreNormalComplex_circleMeridian, hwnorm]
        simp only [Complex.norm_real]
        rw [Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ (1 / 4 : ℝ) := by ring_nf; norm_num
  · have ha : 0 ≤ 2 - 2 * (t : ℝ) := by linarith
    have hb : 0 ≤ 2 * (t : ℝ) - 1 := by linarith
    have hn1 := rightTubeCoreInputNormalRadiusBound p.1 p.2.1
    calc
      ‖((2 - 2 * (t : ℝ) : ℝ) : ℂ) * zeroHeightSignedImaginaryWaypoint p +
          ((2 * (t : ℝ) - 1 : ℝ) : ℂ) * rightTubeCoreNormalComplex p.1‖
          ≤ ‖((2 - 2 * (t : ℝ) : ℝ) : ℂ) *
                zeroHeightSignedImaginaryWaypoint p‖ +
              ‖((2 * (t : ℝ) - 1 : ℝ) : ℂ) *
                rightTubeCoreNormalComplex p.1‖ := norm_add_le _ _
      _ = (2 - 2 * (t : ℝ)) * (1 / 8 : ℝ) +
            (2 * (t : ℝ) - 1) * ‖rightTubeCoreNormalComplex p.1‖ := by
        rw [norm_mul, norm_mul, hwnorm]
        simp only [Complex.norm_real]
        rw [Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ (1 / 4 : ℝ) := by nlinarith

theorem zeroHeightCoreNormalDetour_im_ne_zero_of_interior
    (p : RightTubeMinusLeftCore) (hheight : p.1 2 = 0)
    (t : unitInterval) (ht0 : (t : ℝ) ≠ 0) (ht1 : (t : ℝ) ≠ 1) :
    (zeroHeightCoreNormalDetour t p).im ≠ 0 := by
  obtain ⟨hn0im, hn1im⟩ :=
    realEndpoints_zeroHeight_rightTubeCoreNormals p hheight
  obtain ⟨hwnorm, hwim⟩ :=
    zeroHeight_signedImaginaryWaypoint_properties p hheight
  unfold zeroHeightCoreNormalDetour
  split_ifs with hhalf
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, hn0im, mul_zero, zero_add]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ht0) hwim
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, hn1im, mul_zero, add_zero]
    apply mul_ne_zero
    · intro h
      apply ht1
      linarith
    · exact hwim

theorem zeroHeightEndpointAvoidance_coreNormalDetour
    (p : RightTubeMinusLeftCore) :
    rightTubeCorePolarReconstruction (1 : Circle)
          (zeroHeightCoreNormalDetour 0 p) ∉ Set.range
            ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_leftCore ∧
      rightTubeCorePolarReconstruction (rightTubeCoreAngularCoordinate p)
          (zeroHeightCoreNormalDetour 1 p) ∉ Set.range
            ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_leftCore := by
  obtain ⟨hn0, hn1, hmid⟩ := zeroHeightCoreNormalDetour_endpoints_midpoint p
  constructor
  · rw [hn0, rightCorePolarReconstruction_circleMeridian]
    exact (ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_circleMeridian_mem_rightTubeMinusLeftCore
      (rightTubeMeridianCoordinate p)).2
  · rw [hn1]
    rw [show rightTubeCorePolarReconstruction (rightTubeCoreAngularCoordinate p)
        (rightTubeCoreNormalComplex p.1) = p.1 by
      simpa [rightTubeCoreAngularCoordinate] using
        rightTubeCorePolarReconstruction_self p.1 p.2.1]
    exact p.2.2

theorem zeroHeightCoupledDetour_avoidsLeftCore
    (p : RightTubeMinusLeftCore) (hheight : p.1 2 = 0)
    (t : unitInterval) (u : Circle)
    (hzero : (t : ℝ) = 0 → u = 1)
    (hone : (t : ℝ) = 1 → u = rightTubeCoreAngularCoordinate p) :
    rightTubeCorePolarReconstruction u (zeroHeightCoreNormalDetour t p) ∉
      Set.range ConstructionTargets.T02A03GeometricTubeCover.apm_t02a03_leftCore := by
  by_cases ht0 : (t : ℝ) = 0
  · have ht : t = 0 := Subtype.ext ht0
    subst t
    rw [hzero rfl]
    exact (zeroHeightEndpointAvoidance_coreNormalDetour p).1
  by_cases ht1 : (t : ℝ) = 1
  · have ht : t = 1 := Subtype.ext ht1
    subst t
    rw [hone rfl]
    exact (zeroHeightEndpointAvoidance_coreNormalDetour p).2
  · apply reconstructionAvoidsLeftCore_rightTubeCorePolar_of_im_ne_zero
    exact zeroHeightCoreNormalDetour_im_ne_zero_of_interior p hheight t ht0 ht1

theorem zeroHeightAmbientDetour_of_coupledAngular
    (A : C(unitInterval × RightTubeMinusLeftCore, Circle))
    (hA0 : ∀ p, A (0, p) = 1)
    (hA1 : ∀ p, A (1, p) = rightTubeCoreAngularCoordinate p) :
    ∃ H : C(unitInterval × RightTubeMinusLeftCore, apm_t02a03_E3),
      (∀ p, H (0, p) = apm_t02a03_circleMeridian
        (rightTubeMeridianCoordinate p)) ∧
      (∀ p, H (1, p) = p.1) ∧
      (∀ tp, tp.2.1 2 = 0 → H tp ∈ apm_t02a03_rightTube) ∧
      (∀ tp, tp.2.1 2 = 0 → H tp ∉ Set.range apm_t02a03_leftCore) := by
  let H : C(unitInterval × RightTubeMinusLeftCore, apm_t02a03_E3) :=
    ⟨fun tp => rightTubeCorePolarReconstruction (A tp)
        (zeroHeightCoreNormalDetour tp.1 tp.2),
      rightTubeCoreTubularCoordinates_continuous.2.comp
        (A.continuous.prodMk continuous_zeroHeightCoreNormalDetour)⟩
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro p
    simp only [H, ContinuousMap.coe_mk]
    rw [hA0, (zeroHeightCoreNormalDetour_endpoints_midpoint p).1,
      rightCorePolarReconstruction_circleMeridian]
  · intro p
    simp only [H, ContinuousMap.coe_mk]
    rw [hA1, (zeroHeightCoreNormalDetour_endpoints_midpoint p).2.1]
    simpa [rightTubeCoreAngularCoordinate] using
      rightTubeCorePolarReconstruction_self p.1 p.2.1
  · intro tp hheight
    apply reconstructionMemRightTube_rightTubeCorePolar
    exact zeroHeightCoreNormalDetour_radius_le tp.2 hheight tp.1
  · intro tp hheight
    apply zeroHeightCoupledDetour_avoidsLeftCore tp.2 hheight tp.1 (A tp)
    · intro ht
      have htp : tp = (0, tp.2) := by
        apply Prod.ext
        · exact Subtype.ext ht
        · rfl
      rw [htp]
      exact hA0 tp.2
    · intro ht
      have htp : tp = (1, tp.2) := by
        apply Prod.ext
        · exact Subtype.ext ht
        · rfl
      rw [htp]
      exact hA1 tp.2

theorem continuousCoupledAngularComplexInterpolation_exists :
    ∃ Z : C(unitInterval × RightTubeMinusLeftCore, ℂ),
      (∀ p, Z (0, p) = 1) ∧
      (∀ p, Z (1, p) = rightTubeCorePlanarComplex p.1) := by
  let Z : C(unitInterval × RightTubeMinusLeftCore, ℂ) :=
    ⟨fun tp => ((1 - (tp.1 : ℝ) : ℝ) : ℂ) +
        ((tp.1 : ℝ) : ℂ) * rightTubeCorePlanarComplex tp.2.1, by
      unfold rightTubeCorePlanarComplex
      fun_prop⟩
  refine ⟨Z, ?_, ?_⟩
  · intro p
    simp [Z]
  · intro p
    simp [Z]

noncomputable def coupledAngularComplexInterpolation
    (tp : unitInterval × RightTubeMinusLeftCore) : ℂ :=
  ((1 - (tp.1 : ℝ) : ℝ) : ℂ) +
    ((tp.1 : ℝ) : ℂ) * rightTubeCorePlanarComplex tp.2.1

theorem coupledAngularComplexInterpolation_eq_zero_iff
    (tp : unitInterval × RightTubeMinusLeftCore) :
    coupledAngularComplexInterpolation tp = 0 ↔
      (rightTubeCorePlanarComplex tp.2.1).im = 0 ∧
      1 - (tp.1 : ℝ) + (tp.1 : ℝ) *
        (rightTubeCorePlanarComplex tp.2.1).re = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [coupledAngularComplexInterpolation] at hre him
    constructor
    · by_contra hw
      have ht0 : tp.1 = 0 := him.resolve_right hw
      have ht : (tp.1 : ℝ) = 0 := congrArg Subtype.val ht0
      rw [ht] at hre
      norm_num at hre
    · exact hre
  · rintro ⟨him, hre⟩
    apply Complex.ext
    · simpa [coupledAngularComplexInterpolation] using hre
    · simp [coupledAngularComplexInterpolation, him]

theorem coupledAngularComplexInterpolation_zero_interior
    (tp : unitInterval × RightTubeMinusLeftCore)
    (hz : coupledAngularComplexInterpolation tp = 0) :
    0 < (tp.1 : ℝ) ∧ (tp.1 : ℝ) < 1 ∧
      (rightTubeCorePlanarComplex tp.2.1).re < 0 := by
  have hzero := (coupledAngularComplexInterpolation_eq_zero_iff tp).mp hz
  rcases hzero with ⟨him, hre⟩
  have ht0 : 0 < (tp.1 : ℝ) := by
    have hnonneg := tp.1.2.1
    apply lt_of_le_of_ne hnonneg
    intro ht
    rw [ht.symm] at hre
    norm_num at hre
  have ht1 : (tp.1 : ℝ) < 1 := by
    have hle := tp.1.2.2
    apply lt_of_le_of_ne hle
    intro ht
    rw [ht] at hre
    norm_num at hre
    apply rightTubeCorePlanarComplex_ne_zero tp.2.1 tp.2.2.1
    apply Complex.ext
    · simpa using hre
    · simpa using him
  refine ⟨ht0, ht1, ?_⟩
  nlinarith

theorem coupledAngular_of_nonvanishingComplexPath
    (Z : C(unitInterval × RightTubeMinusLeftCore, ℂ))
    (hZ : ∀ tp, Z tp ≠ 0)
    (hZ0 : ∀ p, Z (0, p) = 1)
    (hZ1 : ∀ p, Z (1, p) = rightTubeCorePlanarComplex p.1) :
    ∃ A : C(unitInterval × RightTubeMinusLeftCore, Circle),
      (∀ p, A (0, p) = 1) ∧
      (∀ p, A (1, p) = rightTubeCoreAngularCoordinate p) := by
  let A : C(unitInterval × RightTubeMinusLeftCore, Circle) :=
    ⟨fun tp => ⟨NormedSpace.normalize (Z tp),
        mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hZ tp))⟩, by
      apply Continuous.subtype_mk
      rw [continuous_iff_continuousAt]
      intro tp
      exact ((continuous_norm.comp Z.continuous).continuousAt.inv₀
        (norm_ne_zero_iff.mpr (hZ tp))).smul Z.continuous.continuousAt⟩
  refine ⟨A, ?_, ?_⟩
  · intro p
    apply Subtype.ext
    simp only [A, ContinuousMap.coe_mk, hZ0]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (by norm_num)
  · intro p
    apply Subtype.ext
    simp [A, hZ1, rightTubeCoreAngularCoordinate]

noncomputable def coupledAngularWaypointPath
    (W : C(RightTubeMinusLeftCore, ℂ))
    (t : unitInterval) (p : RightTubeMinusLeftCore) : ℂ :=
  if (t : ℝ) ≤ 1 / 2 then
    ((1 - 2 * (t : ℝ) : ℝ) : ℂ) + ((2 * (t : ℝ) : ℝ) : ℂ) * W p
  else
    ((2 - 2 * (t : ℝ) : ℝ) : ℂ) * W p +
      ((2 * (t : ℝ) - 1 : ℝ) : ℂ) * rightTubeCorePlanarComplex p.1

set_option maxHeartbeats 800000 in
theorem nonvanishingComplexPath_of_waypoint
    (W : C(RightTubeMinusLeftCore, ℂ))
    (hleft : ∀ (t : unitInterval) (p : RightTubeMinusLeftCore),
      (t : ℝ) ≤ 1 / 2 →
      ((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * W p ≠ 0)
    (hright : ∀ (t : unitInterval) (p : RightTubeMinusLeftCore),
      ¬ (t : ℝ) ≤ 1 / 2 →
      ((2 - 2 * (t : ℝ) : ℝ) : ℂ) * W p +
        ((2 * (t : ℝ) - 1 : ℝ) : ℂ) *
          rightTubeCorePlanarComplex p.1 ≠ 0) :
    ∃ Z : C(unitInterval × RightTubeMinusLeftCore, ℂ),
      (∀ tp, Z tp ≠ 0) ∧ (∀ p, Z (0, p) = 1) ∧
      (∀ p, Z (1, p) = rightTubeCorePlanarComplex p.1) := by
  have hcont : Continuous (fun tp : unitInterval × RightTubeMinusLeftCore =>
      coupledAngularWaypointPath W tp.1 tp.2) := by
    have hW : Continuous (fun tp : unitInterval × RightTubeMinusLeftCore =>
        W tp.2) := W.continuous.comp continuous_snd
    have hp : Continuous (fun tp : unitInterval × RightTubeMinusLeftCore =>
        rightTubeCorePlanarComplex tp.2.1) := by
      unfold rightTubeCorePlanarComplex
      fun_prop
    unfold coupledAngularWaypointPath
    apply continuous_if_le
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · intro tp h
      simp only at h
      rw [h]
      norm_num
  let Z : C(unitInterval × RightTubeMinusLeftCore, ℂ) :=
    ⟨fun tp => coupledAngularWaypointPath W tp.1 tp.2, hcont⟩
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro tp
    change coupledAngularWaypointPath W tp.1 tp.2 ≠ 0
    unfold coupledAngularWaypointPath
    split_ifs with h
    · exact hleft tp.1 tp.2 h
    · exact hright tp.1 tp.2 h
  · intro p
    norm_num [Z, coupledAngularWaypointPath]
  · intro p
    norm_num [Z, coupledAngularWaypointPath]

theorem coupledAngularDepartureLeg_ne_zero_of_waypoint_re_pos
    (W : C(RightTubeMinusLeftCore, ℂ))
    (hW : ∀ p, 0 < (W p).re)
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (ht : (t : ℝ) ≤ 1 / 2) :
    (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * W p) ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  norm_num [Complex.mul_re] at hre
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  by_cases htzero : (t : ℝ) = 0
  · rw [htzero] at hre
    norm_num at hre
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm htzero)
    have hfirst : 0 ≤ 1 - 2 * (t : ℝ) := by linarith
    have hsecond : 0 < 2 * (t : ℝ) * (W p).re :=
      mul_pos (mul_pos (by norm_num) htpos) (hW p)
    linarith

theorem coupledAngularArrivalLeg_ne_zero_of_cross_im_ne_zero
    (W : C(RightTubeMinusLeftCore, ℂ))
    (hcross : ∀ p,
      (conj (W p) * rightTubeCorePlanarComplex p.1).im ≠ 0)
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (ht : ¬ (t : ℝ) ≤ 1 / 2) :
    (((2 - 2 * (t : ℝ) : ℝ) : ℂ) * W p +
        ((2 * (t : ℝ) - 1 : ℝ) : ℂ) *
          rightTubeCorePlanarComplex p.1) ≠ 0 := by
  intro hz
  have hcoeff : 0 < 2 * (t : ℝ) - 1 := by linarith
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  norm_num [Complex.mul_re, Complex.mul_im] at hre him
  have hre' := congrArg (fun x : ℝ => x * (W p).im) hre
  have him' := congrArg (fun x : ℝ => x * (W p).re) him
  have hb : (2 * (t : ℝ) - 1) *
      ((W p).re * (rightTubeCorePlanarComplex p.1).im -
        (W p).im * (rightTubeCorePlanarComplex p.1).re) = 0 := by
    nlinarith [hre', him']
  have hdet : (W p).re * (rightTubeCorePlanarComplex p.1).im -
      (W p).im * (rightTubeCorePlanarComplex p.1).re = 0 :=
    (mul_eq_zero.mp hb).resolve_left hcoeff.ne'
  have hzero : (conj (W p) * rightTubeCorePlanarComplex p.1).im = 0 := by
    simpa only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
      neg_mul, add_comm] using hdet
  exact (hcross p) hzero

theorem coupledAngularArrivalCollision_negative_endpoint
    (W : C(RightTubeMinusLeftCore, ℂ))
    (hW : ∀ p, 0 < (W p).re)
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (ht : ¬ (t : ℝ) ≤ 1 / 2)
    (hz : (((2 - 2 * (t : ℝ) : ℝ) : ℂ) * W p +
        ((2 * (t : ℝ) - 1 : ℝ) : ℂ) *
          rightTubeCorePlanarComplex p.1) = 0) :
    (rightTubeCorePlanarComplex p.1).re < 0 ∧
      (conj (W p) * rightTubeCorePlanarComplex p.1).im = 0 := by
  have ht_half : 1 / 2 < (t : ℝ) := lt_of_not_ge ht
  have ht_one : (t : ℝ) < 1 := by
    apply lt_of_le_of_ne t.2.2
    intro ht1
    have hz1 := hz
    rw [ht1] at hz1
    norm_num at hz1
    exact rightTubeCorePlanarComplex_ne_zero p.1 p.2.1 hz1
  have ha : 0 < 2 - 2 * (t : ℝ) := by linarith
  have hb : 0 < 2 * (t : ℝ) - 1 := by linarith
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  norm_num [Complex.mul_re, Complex.mul_im] at hre him
  constructor
  · have hapos : 0 < (2 - 2 * (t : ℝ)) * (W p).re :=
      mul_pos ha (hW p)
    nlinarith
  · have hre' := congrArg (fun x : ℝ => x * (W p).im) hre
    have him' := congrArg (fun x : ℝ => x * (W p).re) him
    have hdet : (W p).re * (rightTubeCorePlanarComplex p.1).im -
        (W p).im * (rightTubeCorePlanarComplex p.1).re = 0 := by
      have hprod : (2 * (t : ℝ) - 1) *
          ((W p).re * (rightTubeCorePlanarComplex p.1).im -
            (W p).im * (rightTubeCorePlanarComplex p.1).re) = 0 := by
        nlinarith [hre', him']
      exact (mul_eq_zero.mp hprod).resolve_left hb.ne'
    simpa only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
      neg_mul, add_comm] using hdet

theorem coupledAngularArrivalLeg_ne_zero_of_negative_endpoint_cross
    (W : C(RightTubeMinusLeftCore, ℂ))
    (hW : ∀ p, 0 < (W p).re)
    (hcross : ∀ p,
      (rightTubeCorePlanarComplex p.1).re < 0 →
        (conj (W p) * rightTubeCorePlanarComplex p.1).im ≠ 0)
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (ht : ¬ (t : ℝ) ≤ 1 / 2) :
    (((2 - 2 * (t : ℝ) : ℝ) : ℂ) * W p +
        ((2 * (t : ℝ) - 1 : ℝ) : ℂ) *
          rightTubeCorePlanarComplex p.1) ≠ 0 := by
  intro hz
  obtain ⟨hneg, hzero⟩ :=
    coupledAngularArrivalCollision_negative_endpoint W hW t p ht hz
  exact hcross p hneg hzero

theorem rotatedEndpointWaypoint_arrival_ne_zero_exists :
    ∃ W : C(RightTubeMinusLeftCore, ℂ),
      ∀ (t : unitInterval) (p : RightTubeMinusLeftCore),
        ¬ (t : ℝ) ≤ 1 / 2 →
          (((2 - 2 * (t : ℝ) : ℝ) : ℂ) * W p +
            ((2 * (t : ℝ) - 1 : ℝ) : ℂ) *
              rightTubeCorePlanarComplex p.1) ≠ 0 := by
  let W : C(RightTubeMinusLeftCore, ℂ) :=
    ⟨fun p => -Complex.I * rightTubeCorePlanarComplex p.1, by
      apply Continuous.mul continuous_const
      exact (by
        unfold rightTubeCorePlanarComplex
        fun_prop)⟩
  refine ⟨W, ?_⟩
  intro t p ht hz
  have hb : 0 < 2 * (t : ℝ) - 1 := by linarith
  have hfactor :
      ((((2 * (t : ℝ) - 1 : ℝ) : ℂ) -
          ((2 - 2 * (t : ℝ) : ℝ) : ℂ) * Complex.I) *
          rightTubeCorePlanarComplex p.1) = 0 := by
    rw [← hz]
    change _ = (((2 - 2 * (t : ℝ) : ℝ) : ℂ) *
      (-Complex.I * rightTubeCorePlanarComplex p.1) + _)
    ring
  rcases mul_eq_zero.mp hfactor with hcoeff | hv
  · have hre := congrArg Complex.re hcoeff
    norm_num at hre
    linarith
  · exact rightTubeCorePlanarComplex_ne_zero p.1 p.2.1 hv

noncomputable def rotatedEndpointWaypoint
    (p : RightTubeMinusLeftCore) : ℂ :=
  -Complex.I * rightTubeCorePlanarComplex p.1

/-- The rotated endpoint waypoint as a continuous family.  This is the
waypoint input needed by `nonvanishingComplexPath_of_waypoint` once its
departure leg has been corrected away from zero. -/
noncomputable def rotatedEndpointWaypointMap :
    C(RightTubeMinusLeftCore, ℂ) :=
  ⟨rotatedEndpointWaypoint, by
    apply Continuous.mul continuous_const
    unfold rightTubeCorePlanarComplex
    fun_prop⟩

@[simp] theorem rotatedEndpointWaypointMap_apply
    (p : RightTubeMinusLeftCore) :
    rotatedEndpointWaypointMap p = rotatedEndpointWaypoint p := rfl

theorem rotatedEndpointWaypoint_departure_eq_zero_iff
    (t : unitInterval) (p : RightTubeMinusLeftCore) :
    (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) *
          rotatedEndpointWaypoint p) = 0 ↔
      (rightTubeCorePlanarComplex p.1).re = 0 ∧
        1 - 2 * (t : ℝ) +
          2 * (t : ℝ) * (rightTubeCorePlanarComplex p.1).im = 0 := by
  constructor
  · intro hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp [rotatedEndpointWaypoint, Complex.mul_re, Complex.mul_im] at hre him
    rcases him with htzero | hvre
    · subst t
      norm_num at hre
    · exact ⟨hvre, hre⟩
  · rintro ⟨hvre, hre⟩
    apply Complex.ext
    · simpa [rotatedEndpointWaypoint, Complex.mul_re, Complex.mul_im]
        using hre
    · simp [rotatedEndpointWaypoint, Complex.mul_re, Complex.mul_im, hvre]

theorem rotatedEndpointWaypoint_departure_zero_time_pos
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
      ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p) = 0) :
    0 < (t : ℝ) := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  by_contra ht
  have ht' : (t : ℝ) = 0 := le_antisymm (le_of_not_gt ht) ht0
  have := hz
  rw [ht'] at this
  norm_num at this

theorem rotatedEndpointWaypoint_departure_zero_time_lt_half
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (ht : (t : ℝ) ≤ 1 / 2)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
      ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p) = 0) :
    (t : ℝ) < 1 / 2 := by
  by_contra hlt
  have ht' : (t : ℝ) = 1 / 2 := le_antisymm ht (le_of_not_gt hlt)
  rw [ht'] at hz
  norm_num [rotatedEndpointWaypoint] at hz
  exact rightTubeCorePlanarComplex_ne_zero p.1 p.2.1 hz

theorem rotatedEndpointWaypoint_departure_zero_support_pos
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (ht : (t : ℝ) ≤ 1 / 2)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
      ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p) = 0) :
    0 < (t : ℝ) * (1 - 2 * (t : ℝ)) := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have htpos : 0 < (t : ℝ) := by
    by_contra h
    have htzero : (t : ℝ) = 0 := le_antisymm (le_of_not_gt h) ht0
    rw [htzero] at hz
    norm_num at hz
  have hthalf : (t : ℝ) < 1 / 2 := by
    by_contra h
    have heq : (t : ℝ) = 1 / 2 := le_antisymm ht (le_of_not_gt h)
    rw [heq] at hz
    norm_num [rotatedEndpointWaypoint] at hz
    exact rightTubeCorePlanarComplex_ne_zero p.1 p.2.1 hz
  exact mul_pos htpos (by linarith)

/-- The natural endpoint-fixed transverse term is nonzero at every zero of
the uncorrected departure leg.  A subsequent global zero-locus argument must
still show that this correction creates no new zeros. -/
theorem rotatedEndpointWaypoint_transverse_correction_ne_zero_at_departure_zero
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (ht : (t : ℝ) ≤ 1 / 2)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
      ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p) = 0) :
    (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p +
        (((t : ℝ) * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  rw [hz, zero_add]
  intro h
  have him : (t : ℝ) * (1 - 2 * (t : ℝ)) = 0 := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero,
      Complex.zero_im] using congrArg Complex.im h
  have hpos := rotatedEndpointWaypoint_departure_zero_support_pos t p ht hz
  exact (ne_of_gt hpos) him

/-- Exact zero locus after adding the endpoint-fixed transverse correction.
This is the remaining quantitative target for ruling out newly created
zeros using the right-tube coordinate bounds. -/
theorem rotatedEndpointWaypoint_corrected_departure_eq_zero_iff
    (t : unitInterval) (p : RightTubeMinusLeftCore) :
    (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p +
        (((t : ℝ) * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = 0 ↔
      1 - 2 * (t : ℝ) +
          2 * (t : ℝ) * (rightTubeCorePlanarComplex p.1).im = 0 ∧
        -2 * (t : ℝ) * (rightTubeCorePlanarComplex p.1).re +
          (t : ℝ) * (1 - 2 * (t : ℝ)) = 0 := by
  constructor
  · intro h
    constructor
    · simpa [rotatedEndpointWaypoint, Complex.mul_re, Complex.mul_im]
        using congrArg Complex.re h
    · simpa [rotatedEndpointWaypoint, Complex.mul_re, Complex.mul_im]
        using congrArg Complex.im h
  · rintro ⟨hre, him⟩
    apply Complex.ext
    · simpa [rotatedEndpointWaypoint, Complex.mul_re, Complex.mul_im]
        using hre
    · simpa [rotatedEndpointWaypoint, Complex.mul_re, Complex.mul_im]
        using him

/-- A zero of the transversely corrected departure leg occurs at positive
time and forces explicit real and imaginary coordinates. -/
theorem rotatedEndpointWaypoint_corrected_departure_zero_coordinates
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p +
        (((t : ℝ) * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = 0) :
    0 < (t : ℝ) ∧
      (rightTubeCorePlanarComplex p.1).re = (1 - 2 * (t : ℝ)) / 2 ∧
      (rightTubeCorePlanarComplex p.1).im =
        -(1 - 2 * (t : ℝ)) / (2 * (t : ℝ)) := by
  have heq :=
    (rotatedEndpointWaypoint_corrected_departure_eq_zero_iff t p).mp hz
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have htpos : 0 < (t : ℝ) := by
    by_contra h
    have htzero : (t : ℝ) = 0 := le_antisymm (le_of_not_gt h) ht0
    rw [htzero] at heq
    norm_num at heq
  refine ⟨htpos, ?_, ?_⟩
  · nlinarith [heq.2]
  · field_simp
    nlinarith [heq.1]

/-- The scalar norm constraint forced by a zero of the corrected departure
leg.  Together with `rightTubeCoreInputNormalRadiusBound`, this reduces the
remaining exclusion question to a one-variable estimate. -/
theorem rotatedEndpointWaypoint_corrected_departure_zero_normSq
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p +
        (((t : ℝ) * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = 0) :
    Complex.normSq (rightTubeCorePlanarComplex p.1) =
      (1 - 2 * (t : ℝ)) ^ 2 / 4 +
        (1 - 2 * (t : ℝ)) ^ 2 / (4 * (t : ℝ) ^ 2) := by
  obtain ⟨ht, hre, him⟩ :=
    rotatedEndpointWaypoint_corrected_departure_zero_coordinates t p hz
  rw [Complex.normSq_apply, hre, him]
  field_simp
  ring

/-- Any zero of the corrected departure leg must place its scalar
norm-square expression inside the right-tube annulus bounds. -/
theorem rotatedEndpointWaypoint_corrected_departure_zero_scalar_bounds
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p +
        (((t : ℝ) * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = 0) :
    (9 / 16 : ℝ) ≤
        (1 - 2 * (t : ℝ)) ^ 2 / 4 +
          (1 - 2 * (t : ℝ)) ^ 2 / (4 * (t : ℝ) ^ 2) ∧
      (1 - 2 * (t : ℝ)) ^ 2 / 4 +
          (1 - 2 * (t : ℝ)) ^ 2 / (4 * (t : ℝ) ^ 2) ≤ (25 / 16 : ℝ) := by
  have heq := rotatedEndpointWaypoint_corrected_departure_zero_normSq t p hz
  have hb := rightTubeCorePlanarNormBounds p.1 p.2.1
  have hn : 0 ≤ ‖rightTubeCorePlanarComplex p.1‖ := norm_nonneg _
  rw [← heq, ← Complex.sq_norm]
  constructor <;> nlinarith

/-- Denominator-free polynomial constraints on every possible zero time of
the corrected departure leg. -/
theorem rotatedEndpointWaypoint_corrected_departure_zero_polynomial_bounds
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p +
        (((t : ℝ) * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = 0) :
    9 * (t : ℝ) ^ 2 ≤
        4 * (1 - 2 * (t : ℝ)) ^ 2 * (t : ℝ) ^ 2 +
          4 * (1 - 2 * (t : ℝ)) ^ 2 ∧
      4 * (1 - 2 * (t : ℝ)) ^ 2 * (t : ℝ) ^ 2 +
          4 * (1 - 2 * (t : ℝ)) ^ 2 ≤ 25 * (t : ℝ) ^ 2 := by
  have ht :=
    (rotatedEndpointWaypoint_corrected_departure_zero_coordinates t p hz).1
  have hb :=
    rotatedEndpointWaypoint_corrected_departure_zero_scalar_bounds t p hz
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  field_simp [htne] at hb ⊢
  constructor <;> nlinarith [hb.1, hb.2]

/-- The annulus bound excludes corrected departure zeros near the initial
endpoint. -/
theorem rotatedEndpointWaypoint_corrected_departure_zero_time_gt_eighth
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p +
        (((t : ℝ) * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = 0) :
    (1 / 8 : ℝ) < (t : ℝ) := by
  have hc :=
    rotatedEndpointWaypoint_corrected_departure_zero_coordinates t p hz
  have hb := rightTubeCorePlanarNormBounds p.1 p.2.1
  have himabs :
      |(rightTubeCorePlanarComplex p.1).im| ≤ (5 / 4 : ℝ) :=
    (RCLike.abs_im_le_norm (rightTubeCorePlanarComplex p.1)).trans hb.2
  have himlo := (abs_le.mp himabs).1
  have himhi := (abs_le.mp himabs).2
  by_contra h
  have htupper : (t : ℝ) ≤ 1 / 8 := le_of_not_gt h
  have hmullo : 0 ≤ (t : ℝ) *
      ((rightTubeCorePlanarComplex p.1).im + 5 / 4) :=
    mul_nonneg (le_of_lt hc.1) (by linarith)
  have hmulhi : 0 ≤ (t : ℝ) *
      (5 / 4 - (rightTubeCorePlanarComplex p.1).im) :=
    mul_nonneg (le_of_lt hc.1) (by linarith)
  have heq :=
    (rotatedEndpointWaypoint_corrected_departure_eq_zero_iff t p).mp hz
  nlinarith [hmullo, hmulhi]

/-- The inner annulus bound also excludes corrected departure zeros near the
midpoint endpoint. -/
theorem rotatedEndpointWaypoint_corrected_departure_zero_time_lt_three_eighths
    (t : unitInterval) (p : RightTubeMinusLeftCore)
    (ht_half : (t : ℝ) ≤ 1 / 2)
    (hz : (((1 - 2 * (t : ℝ) : ℝ) : ℂ) +
        ((2 * (t : ℝ) : ℝ) : ℂ) * rotatedEndpointWaypoint p +
        (((t : ℝ) * (1 - 2 * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = 0) :
    (t : ℝ) < (3 / 8 : ℝ) := by
  have hp :=
    rotatedEndpointWaypoint_corrected_departure_zero_polynomial_bounds t p hz
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  by_contra h
  have htlo : (3 / 8 : ℝ) ≤ (t : ℝ) := le_of_not_gt h
  have hs0 : 0 ≤ 1 - 2 * (t : ℝ) := by linarith
  have hs_sq : (1 - 2 * (t : ℝ)) ^ 2 ≤ (1 / 16 : ℝ) := by
    nlinarith [sq_nonneg (1 - 2 * (t : ℝ))]
  have ht_sq : (t : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hprod :
      (1 - 2 * (t : ℝ)) ^ 2 * ((t : ℝ) ^ 2 + 1) ≤
        (1 / 16 : ℝ) * 2 := by
    calc
      _ ≤ (1 - 2 * (t : ℝ)) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
      _ ≤ (1 / 16 : ℝ) * 2 := mul_le_mul_of_nonneg_right hs_sq (by norm_num)
  nlinarith [hp.1, sq_nonneg ((t : ℝ) - 3 / 8)]

/-- Continuous scalar support for a second correction, confined to the only
time window in which the first correction can vanish. -/
noncomputable def correctedDepartureBump (t : unitInterval) : ℝ :=
  max 0 (((t : ℝ) - 1 / 8) * (3 / 8 - (t : ℝ)))

theorem continuous_correctedDepartureBump :
    Continuous correctedDepartureBump := by
  unfold correctedDepartureBump
  fun_prop

theorem correctedDepartureBump_pos
    (t : unitInterval) (hlo : (1 / 8 : ℝ) < (t : ℝ))
    (hhi : (t : ℝ) < (3 / 8 : ℝ)) :
    0 < correctedDepartureBump t := by
  rw [correctedDepartureBump, max_eq_right]
  · exact mul_pos (by linarith) (by linarith)
  · exact le_of_lt (mul_pos (by linarith) (by linarith))

@[simp] theorem correctedDepartureBump_zero :
    correctedDepartureBump 0 = 0 := by
  norm_num [correctedDepartureBump]

@[simp] theorem correctedDepartureBump_one :
    correctedDepartureBump 1 = 0 := by
  norm_num [correctedDepartureBump]

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
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCoreTubularCoordinates_continuous
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCoreAngularCoordinate
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCoreNormalInterpolation_exists
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.norm_rightTubeCoreNormalComplex_circleMeridian
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCore_radial_error_le
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCoreInputNormalRadiusBound
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCorePlanarNormBounds
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCoreInterpolatedNormalRadiusBound
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.normalizedRightCorePlanar_circleMeridian
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightCorePolarReconstruction_circleMeridian
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeRadialCoefficient_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeRadialNormalInterpolation_exists
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.specializedRightTubeRadialNormalInterpolation_exists
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeRadialAmbientDeformation_endpoints
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.positiveReconstructionRadius_rightTubeRadialNormalInterpolation
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.recoveredNormal_rightTubeRadialAmbientDeformation
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.avoidsLeftCore_rightTubeRadialAmbientDeformation
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.reconstructionMemRightTube_rightTubeCorePolar
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeCoreRadialAmbientDeformation_exists
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.reconstructionAvoidsLeftCore_rightTubeCorePolar_of_im_ne_zero
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.corePolar_leftCore_collision_equation
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.collisionPolynomial_ne_implies_avoidsLeftCore_rightTubeCorePolar
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.collisionPolynomial_pos_of_normal_re_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.nonpositiveNormalSafeCorridor_collisionPolynomial_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeightCollisionPolynomial_eq_zero_implies_leftCore
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.inputZeroHeight_collisionPolynomial_ne
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.meridianStart_collisionPolynomial_factor
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.inputCollisionPolynomial_factor_rightTubeNormalReal
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.inputCollisionPolynomial_positiveFactor_meridianReal
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.collisionEndpoint_positiveFactor_signBridge
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rightTubeMeridianCoordinate_im_positiveFactor_height
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.nonzeroHeight_im_ne_zero_rightTubeCoreNormalInterpolation
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.nonzeroHeight_avoidsLeftCore_rightTubeCoreRadialAmbient
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeight_rightTubeMeridianCoordinate_re_sq
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.signCases_zeroHeight_rightTubeMeridianCoordinate_re
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.positiveSign_rightTubeNormalComplex_re_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.positiveSign_radialStart_collisionPolynomial_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.positiveSign_input_collisionPolynomial_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.realEndpoints_zeroHeight_rightTubeCoreNormals
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeight_signedImaginaryWaypoint_properties
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.coreNormalAffineLeg_radius_and_im_ne_zero
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeight_specializedCoreNormalAffineLegs_radius_and_im_ne_zero
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeightCoreNormalDetour_endpoints_midpoint
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.continuous_zeroHeightCoreNormalDetour
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeightCoreNormalDetour_radius_le
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeightCoreNormalDetour_im_ne_zero_of_interior
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeightEndpointAvoidance_coreNormalDetour
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeightCoupledDetour_avoidsLeftCore
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.zeroHeightAmbientDetour_of_coupledAngular
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.continuousCoupledAngularComplexInterpolation_exists
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.coupledAngularComplexInterpolation_eq_zero_iff
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.coupledAngularComplexInterpolation_zero_interior
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.coupledAngular_of_nonvanishingComplexPath
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.nonvanishingComplexPath_of_waypoint
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.coupledAngularDepartureLeg_ne_zero_of_waypoint_re_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.coupledAngularArrivalLeg_ne_zero_of_cross_im_ne_zero
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.coupledAngularArrivalCollision_negative_endpoint
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.coupledAngularArrivalLeg_ne_zero_of_negative_endpoint_cross
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_arrival_ne_zero_exists
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_departure_eq_zero_iff
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_departure_zero_time_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_departure_zero_time_lt_half
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_departure_zero_support_pos
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_transverse_correction_ne_zero_at_departure_zero
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_corrected_departure_eq_zero_iff
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_corrected_departure_zero_coordinates
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_corrected_departure_zero_normSq
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_corrected_departure_zero_scalar_bounds
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_corrected_departure_zero_polynomial_bounds
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_corrected_departure_zero_time_gt_eighth
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.rotatedEndpointWaypoint_corrected_departure_zero_time_lt_three_eighths
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.continuous_correctedDepartureBump
#print axioms ConstructionTargets.T02A03GeometricTubeDeformation.correctedDepartureBump_pos
