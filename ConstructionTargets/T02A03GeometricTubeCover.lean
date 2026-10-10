import Mathlib

noncomputable section

namespace ConstructionTargets.T02A03GeometricTubeCover

abbrev apm_t02a03_E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def apm_t02a03_leftCore (t : ℝ) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![-1 + Real.cos t, Real.sin t, 0]

noncomputable def apm_t02a03_rightCore (t : ℝ) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![1 - Real.cos t, Real.sin t, 0]

def apm_t02a03_genusTwoSpine : Set apm_t02a03_E3 :=
  Set.range apm_t02a03_leftCore ∪ Set.range apm_t02a03_rightCore

def apm_t02a03_W : Set apm_t02a03_E3 :=
  {p | Metric.infDist p apm_t02a03_genusTwoSpine ≤ (1 / 4 : ℝ)}

def apm_t02a03_leftTube : Set apm_t02a03_E3 :=
  Metric.cthickening (1 / 4 : ℝ) (Set.range apm_t02a03_leftCore)

def apm_t02a03_rightTube : Set apm_t02a03_E3 :=
  Metric.cthickening (1 / 4 : ℝ) (Set.range apm_t02a03_rightCore)

theorem apm_t02a03_genusTwoSpine_nonempty :
    apm_t02a03_genusTwoSpine.Nonempty := by
  exact ⟨apm_t02a03_leftCore 0, Set.mem_union_left _ ⟨0, rfl⟩⟩

/-- Exact normalization of the frozen `infDist` neighborhood as the union of
the two closed radius-`1/4` core tubes. -/
theorem apm_t02a03_W_eq_leftTube_union_rightTube :
    apm_t02a03_W = apm_t02a03_leftTube ∪ apm_t02a03_rightTube := by
  rw [apm_t02a03_leftTube, apm_t02a03_rightTube,
    ← Metric.cthickening_union]
  ext p
  change Metric.infDist p apm_t02a03_genusTwoSpine ≤ (1 / 4 : ℝ) ↔
    Metric.infEDist p apm_t02a03_genusTwoSpine ≤
      ENNReal.ofReal (1 / 4 : ℝ)
  rw [Metric.infDist]
  rw [← ENNReal.toReal_le_toReal
    (Metric.infEDist_ne_top apm_t02a03_genusTwoSpine_nonempty) (by finiteness)]
  norm_num

theorem apm_t02a03_leftCore_zero :
    apm_t02a03_leftCore 0 = (0 : apm_t02a03_E3) := by
  ext i
  fin_cases i <;> simp [apm_t02a03_leftCore]

theorem apm_t02a03_leftCore_planar_radius_sq (t : ℝ) :
    (apm_t02a03_leftCore t 0 + 1) ^ 2 +
      (apm_t02a03_leftCore t 1) ^ 2 = 1 := by
  simp [apm_t02a03_leftCore, Real.cos_sq_add_sin_sq]

noncomputable def apm_t02a03_leftCoreCircle (z : Circle) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![-1 + (z : ℂ).re, (z : ℂ).im, 0]

theorem apm_t02a03_continuous_leftCoreCircle :
    Continuous apm_t02a03_leftCoreCircle := by
  unfold apm_t02a03_leftCoreCircle
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem apm_t02a03_range_leftCoreCircle :
    Set.range apm_t02a03_leftCoreCircle = Set.range apm_t02a03_leftCore := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨Complex.arg (z : ℂ), ?_⟩
    ext i
    fin_cases i
    · simpa [apm_t02a03_leftCoreCircle, apm_t02a03_leftCore,
        Circle.norm_coe] using Complex.cos_arg (Circle.coe_ne_zero z)
    · simpa [apm_t02a03_leftCoreCircle, apm_t02a03_leftCore,
        Circle.norm_coe] using Complex.sin_arg (z : ℂ)
    · simp [apm_t02a03_leftCoreCircle, apm_t02a03_leftCore]
  · rintro ⟨t, rfl⟩
    refine ⟨Circle.exp t, ?_⟩
    ext i
    fin_cases i <;> simp [apm_t02a03_leftCoreCircle, apm_t02a03_leftCore]

theorem apm_t02a03_isCompact_range_leftCore :
    IsCompact (Set.range apm_t02a03_leftCore) := by
  rw [← apm_t02a03_range_leftCoreCircle]
  exact isCompact_range apm_t02a03_continuous_leftCoreCircle

theorem apm_t02a03_leftTube_exists_near_leftCore
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_leftTube) :
    ∃ q ∈ Set.range apm_t02a03_leftCore, dist p q ≤ (1 / 4 : ℝ) := by
  rw [apm_t02a03_leftTube,
    apm_t02a03_isCompact_range_leftCore.cthickening_eq_biUnion_closedBall
      (by norm_num)] at hp
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hp
  rcases hp with ⟨q, hq, hd⟩
  exact ⟨q, hq, by simpa [dist_comm] using hd⟩

theorem apm_t02a03_leftTube_planarCenter_ne_zero
    (p : apm_t02a03_E3) (hp : p ∈ apm_t02a03_leftTube) :
    (p 0 + 1) ^ 2 + (p 1) ^ 2 ≠ 0 := by
  rintro hzero
  have hx : p 0 = -1 := by nlinarith [sq_nonneg (p 0 + 1), sq_nonneg (p 1)]
  have hy : p 1 = 0 := by nlinarith [sq_nonneg (p 0 + 1), sq_nonneg (p 1)]
  obtain ⟨q, ⟨t, rfl⟩, hd⟩ :=
    apm_t02a03_leftTube_exists_near_leftCore p hp
  rw [dist_eq_norm, EuclideanSpace.norm_eq] at hd
  simp [apm_t02a03_leftCore, hx, hy, Fin.sum_univ_succ] at hd
  have hs : 1 ≤ √(Real.cos t ^ 2 + (Real.sin t ^ 2 + p 2 ^ 2)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (p 2)]
  norm_num at hd
  linarith

abbrev apm_t02a03_leftTubeSubtype :=
  {p : apm_t02a03_E3 // p ∈ apm_t02a03_leftTube}

noncomputable def apm_t02a03_leftTubePlanarComplex
    (p : apm_t02a03_leftTubeSubtype) : ℂ :=
  (p.1 0 + 1 : ℂ) + (p.1 1 : ℂ) * Complex.I

theorem apm_t02a03_leftTubePlanarComplex_ne_zero
    (p : apm_t02a03_leftTubeSubtype) :
    apm_t02a03_leftTubePlanarComplex p ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  apply apm_t02a03_leftTube_planarCenter_ne_zero p.1 p.2
  simp [apm_t02a03_leftTubePlanarComplex] at hre him
  simp [hre, him]

noncomputable def apm_t02a03_leftTubeAngular
    (p : apm_t02a03_leftTubeSubtype) : Circle :=
  ⟨NormedSpace.normalize (apm_t02a03_leftTubePlanarComplex p),
    mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize
        (apm_t02a03_leftTubePlanarComplex_ne_zero p))⟩

theorem apm_t02a03_continuous_leftTubeAngular :
    Continuous apm_t02a03_leftTubeAngular := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  have hz : Continuous
      (fun q : apm_t02a03_leftTubeSubtype =>
        apm_t02a03_leftTubePlanarComplex q) := by
    have h0 : Continuous (fun q : apm_t02a03_leftTubeSubtype => q.1 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_subtype_val
    have h1 : Continuous (fun q : apm_t02a03_leftTubeSubtype => q.1 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp continuous_subtype_val
    unfold apm_t02a03_leftTubePlanarComplex
    have hre : Continuous
        (fun q : apm_t02a03_leftTubeSubtype =>
          Complex.ofReal (q.1 0 + 1)) :=
      Complex.continuous_ofReal.comp (h0.add continuous_const)
    have him : Continuous
        (fun q : apm_t02a03_leftTubeSubtype =>
          Complex.ofReal (q.1 1) * Complex.I) :=
      (Complex.continuous_ofReal.comp h1).mul continuous_const
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using hre.add him
  exact ((continuous_norm.comp hz).continuousAt.inv₀
      (norm_ne_zero_iff.mpr (apm_t02a03_leftTubePlanarComplex_ne_zero p))).smul
    hz.continuousAt

noncomputable def apm_t02a03_leftTubeNormalComplex
    (p : apm_t02a03_leftTubeSubtype) : ℂ :=
  (‖apm_t02a03_leftTubePlanarComplex p‖ - 1 : ℂ) +
    (p.1 2 : ℂ) * Complex.I

theorem apm_t02a03_continuous_leftTubeNormalComplex :
    Continuous apm_t02a03_leftTubeNormalComplex := by
  have hz : Continuous
      (fun p : apm_t02a03_leftTubeSubtype =>
        apm_t02a03_leftTubePlanarComplex p) := by
    have h0 : Continuous (fun p : apm_t02a03_leftTubeSubtype => p.1 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_subtype_val
    have h1 : Continuous (fun p : apm_t02a03_leftTubeSubtype => p.1 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp continuous_subtype_val
    unfold apm_t02a03_leftTubePlanarComplex
    have hre : Continuous
        (fun p : apm_t02a03_leftTubeSubtype =>
          Complex.ofReal (p.1 0 + 1)) :=
      Complex.continuous_ofReal.comp (h0.add continuous_const)
    have him : Continuous
        (fun p : apm_t02a03_leftTubeSubtype =>
          Complex.ofReal (p.1 1) * Complex.I) :=
      (Complex.continuous_ofReal.comp h1).mul continuous_const
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using hre.add him
  have h2 : Continuous (fun p : apm_t02a03_leftTubeSubtype => p.1 2) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp continuous_subtype_val
  unfold apm_t02a03_leftTubeNormalComplex
  have hre : Continuous
      (fun p : apm_t02a03_leftTubeSubtype =>
        Complex.ofReal (‖apm_t02a03_leftTubePlanarComplex p‖ - 1)) :=
    Complex.continuous_ofReal.comp ((continuous_norm.comp hz).sub continuous_const)
  have him : Continuous
      (fun p : apm_t02a03_leftTubeSubtype =>
        Complex.ofReal (p.1 2) * Complex.I) :=
    (Complex.continuous_ofReal.comp h2).mul continuous_const
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hre.add him

theorem apm_t02a03_leftTubeNormalComplex_eq_zero_iff
    (p : apm_t02a03_leftTubeSubtype) :
    apm_t02a03_leftTubeNormalComplex p = 0 ↔
      p.1 ∈ Set.range apm_t02a03_leftCore := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [apm_t02a03_leftTubeNormalComplex] at hre him
    let z := apm_t02a03_leftTubePlanarComplex p
    have hz : z ≠ 0 := apm_t02a03_leftTubePlanarComplex_ne_zero p
    have hnorm : ‖z‖ = 1 := by simpa [z] using sub_eq_zero.mp hre
    refine ⟨Complex.arg z, ?_⟩
    ext i
    fin_cases i
    · have hc := Complex.cos_arg hz
      rw [hnorm, div_one] at hc
      simp [apm_t02a03_leftCore, z, apm_t02a03_leftTubePlanarComplex] at hc ⊢
      linarith
    · have hs := Complex.sin_arg z
      rw [hnorm, div_one] at hs
      simpa [apm_t02a03_leftCore, z,
        apm_t02a03_leftTubePlanarComplex] using hs
    · simpa [apm_t02a03_leftCore] using him.symm
  · rintro ⟨t, ht⟩
    have h0 := congrArg (fun q : apm_t02a03_E3 => q 0) ht
    have h1 := congrArg (fun q : apm_t02a03_E3 => q 1) ht
    have h2 := congrArg (fun q : apm_t02a03_E3 => q 2) ht
    simp [apm_t02a03_leftCore] at h0 h1 h2
    have hnorm : ‖apm_t02a03_leftTubePlanarComplex p‖ = 1 := by
      rw [Complex.norm_def]
      have hsq : Complex.normSq (apm_t02a03_leftTubePlanarComplex p) = 1 := by
        rw [Complex.normSq_apply]
        simp [apm_t02a03_leftTubePlanarComplex]
        rw [← h0, ← h1]
        simpa [pow_two] using Real.cos_sq_add_sin_sq t
      rw [hsq]
      norm_num
    apply Complex.ext
    · simp [apm_t02a03_leftTubeNormalComplex]
      exact sub_eq_zero.mpr hnorm
    · simpa [apm_t02a03_leftTubeNormalComplex] using h2.symm

abbrev apm_t02a03_LeftTubeMinusCore :=
  {p : apm_t02a03_E3 //
    p ∈ apm_t02a03_leftTube ∧ p ∉ Set.range apm_t02a03_leftCore}

noncomputable def apm_t02a03_leftTubePuncturedNormal
    (p : apm_t02a03_LeftTubeMinusCore) : {
      z : ℂ // z ≠ 0} :=
  ⟨apm_t02a03_leftTubeNormalComplex ⟨p.1, p.2.1⟩, by
    intro h
    exact p.2.2
      ((apm_t02a03_leftTubeNormalComplex_eq_zero_iff ⟨p.1, p.2.1⟩).mp h)⟩

theorem apm_t02a03_continuous_leftTubePuncturedNormal :
    Continuous apm_t02a03_leftTubePuncturedNormal := by
  apply Continuous.subtype_mk
  have hi : Continuous
      (fun p : apm_t02a03_LeftTubeMinusCore =>
        (⟨p.1, p.2.1⟩ : apm_t02a03_leftTubeSubtype)) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  exact apm_t02a03_continuous_leftTubeNormalComplex.comp hi

noncomputable def apm_t02a03_leftTubeNormalAngular
    (p : apm_t02a03_LeftTubeMinusCore) : Circle :=
  ⟨NormedSpace.normalize (apm_t02a03_leftTubePuncturedNormal p).1,
    mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize
        (apm_t02a03_leftTubePuncturedNormal p).2)⟩

theorem apm_t02a03_continuous_leftTubeNormalAngular :
    Continuous apm_t02a03_leftTubeNormalAngular := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  have hz : Continuous
      (fun q : apm_t02a03_LeftTubeMinusCore =>
        (apm_t02a03_leftTubePuncturedNormal q).1) :=
    continuous_subtype_val.comp
      apm_t02a03_continuous_leftTubePuncturedNormal
  exact ((continuous_norm.comp hz).continuousAt.inv₀
      (norm_ne_zero_iff.mpr
        (apm_t02a03_leftTubePuncturedNormal p).2)).smul hz.continuousAt

noncomputable def apm_t02a03_leftTubeTorusCoordinates
    (p : apm_t02a03_LeftTubeMinusCore) : Circle × Circle :=
  (apm_t02a03_leftTubeAngular ⟨p.1, p.2.1⟩,
    apm_t02a03_leftTubeNormalAngular p)

theorem apm_t02a03_continuous_leftTubeTorusCoordinates :
    Continuous apm_t02a03_leftTubeTorusCoordinates := by
  apply Continuous.prodMk
  · exact apm_t02a03_continuous_leftTubeAngular.comp
      (by
        apply Continuous.subtype_mk
        exact continuous_subtype_val)
  · exact apm_t02a03_continuous_leftTubeNormalAngular

noncomputable def apm_t02a03_leftTubeTorusPoint
    (u : Circle × Circle) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![
    -1 + (1 + (1 / 8 : ℝ) * (u.2 : ℂ).re) * (u.1 : ℂ).re,
    (1 + (1 / 8 : ℝ) * (u.2 : ℂ).re) * (u.1 : ℂ).im,
    (1 / 8 : ℝ) * (u.2 : ℂ).im]

theorem apm_t02a03_continuous_leftTubeTorusPoint :
    Continuous apm_t02a03_leftTubeTorusPoint := by
  unfold apm_t02a03_leftTubeTorusPoint
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem apm_t02a03_dist_leftTubeTorusPoint_leftCoreCircle
    (u : Circle × Circle) :
    dist (apm_t02a03_leftTubeTorusPoint u)
      (apm_t02a03_leftCoreCircle u.1) = (1 / 8 : ℝ) := by
  have ha : ((u.1 : ℂ).re) ^ 2 + ((u.1 : ℂ).im) ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe u.1
  have hb : ((u.2 : ℂ).re) ^ 2 + ((u.2 : ℂ).im) ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe u.2
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [apm_t02a03_leftTubeTorusPoint, apm_t02a03_leftCoreCircle,
    Fin.sum_univ_succ]
  ring_nf
  have hrad :
      (u.2 : ℂ).re ^ 2 * (u.1 : ℂ).re ^ 2 * (1 / 64 : ℝ) +
          (u.2 : ℂ).re ^ 2 * (u.1 : ℂ).im ^ 2 * (1 / 64 : ℝ) +
          (u.2 : ℂ).im ^ 2 * (1 / 64 : ℝ) = (1 / 8 : ℝ) ^ 2 := by
    nlinarith
  rw [hrad]
  rw [Real.sqrt_sq_eq_abs]
  norm_num

theorem apm_t02a03_leftTubeTorusPoint_mem_leftTube
    (u : Circle × Circle) :
    apm_t02a03_leftTubeTorusPoint u ∈ apm_t02a03_leftTube := by
  rw [apm_t02a03_leftTube]
  apply Metric.mem_cthickening_of_dist_le
    (apm_t02a03_leftTubeTorusPoint u)
    (apm_t02a03_leftCoreCircle u.1) (1 / 4 : ℝ)
    (Set.range apm_t02a03_leftCore)
  · rw [← apm_t02a03_range_leftCoreCircle]
    exact ⟨u.1, rfl⟩
  · rw [apm_t02a03_dist_leftTubeTorusPoint_leftCoreCircle]
    norm_num

theorem apm_t02a03_leftTubeTorusPoint_not_mem_leftCore
    (u : Circle × Circle) :
    apm_t02a03_leftTubeTorusPoint u ∉ Set.range apm_t02a03_leftCore := by
  let p : apm_t02a03_leftTubeSubtype :=
    ⟨apm_t02a03_leftTubeTorusPoint u,
      apm_t02a03_leftTubeTorusPoint_mem_leftTube u⟩
  have hplanar : apm_t02a03_leftTubePlanarComplex p =
      ((1 + (1 / 8 : ℝ) * (u.2 : ℂ).re : ℝ) : ℂ) * (u.1 : ℂ) := by
    apply Complex.ext <;>
      simp [p, apm_t02a03_leftTubePlanarComplex,
        apm_t02a03_leftTubeTorusPoint]
  have hbre : -(1 : ℝ) ≤ (u.2 : ℂ).re := by
    have h := Complex.abs_re_le_norm (u.2 : ℂ)
    rw [Circle.norm_coe] at h
    exact (abs_le.mp h).1
  have hrnonneg : 0 ≤ 1 + (1 / 8 : ℝ) * (u.2 : ℂ).re := by
    linarith
  have hnorm : ‖apm_t02a03_leftTubePlanarComplex p‖ =
      1 + (1 / 8 : ℝ) * (u.2 : ℂ).re := by
    rw [hplanar, norm_mul, Circle.norm_coe, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnonneg]
  intro hcore
  have hzero :=
    (apm_t02a03_leftTubeNormalComplex_eq_zero_iff p).2 hcore
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp [apm_t02a03_leftTubeNormalComplex] at hre
  rw [hnorm] at hre
  simp [apm_t02a03_leftTubeNormalComplex, p,
    apm_t02a03_leftTubeTorusPoint] at him
  have hb : ((u.2 : ℂ).re) ^ 2 + ((u.2 : ℂ).im) ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe u.2
  nlinarith

noncomputable def apm_t02a03_leftTubeTorusInverse :
    C(Circle × Circle, apm_t02a03_LeftTubeMinusCore) where
  toFun u := ⟨apm_t02a03_leftTubeTorusPoint u,
    apm_t02a03_leftTubeTorusPoint_mem_leftTube u,
    apm_t02a03_leftTubeTorusPoint_not_mem_leftCore u⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact apm_t02a03_continuous_leftTubeTorusPoint

theorem apm_t02a03_leftTubeAngular_torusInverse
    (u : Circle × Circle) :
    apm_t02a03_leftTubeAngular
      ⟨(apm_t02a03_leftTubeTorusInverse u).1,
        (apm_t02a03_leftTubeTorusInverse u).2.1⟩ = u.1 := by
  apply Subtype.ext
  have hbre : -(1 : ℝ) ≤ (u.2 : ℂ).re := by
    have h := Complex.abs_re_le_norm (u.2 : ℂ)
    rw [Circle.norm_coe] at h
    exact (abs_le.mp h).1
  have hrpos : 0 < 1 + (1 / 8 : ℝ) * (u.2 : ℂ).re := by linarith
  change NormedSpace.normalize
      (apm_t02a03_leftTubePlanarComplex
        ⟨apm_t02a03_leftTubeTorusPoint u,
          apm_t02a03_leftTubeTorusPoint_mem_leftTube u⟩) = (u.1 : ℂ)
  rw [show apm_t02a03_leftTubePlanarComplex
      ⟨apm_t02a03_leftTubeTorusPoint u,
        apm_t02a03_leftTubeTorusPoint_mem_leftTube u⟩ =
      (1 + (1 / 8 : ℝ) * (u.2 : ℂ).re) • (u.1 : ℂ) by
    apply Complex.ext <;>
      simp [apm_t02a03_leftTubePlanarComplex,
        apm_t02a03_leftTubeTorusPoint]]
  exact (NormedSpace.normalize_smul_of_pos hrpos (u.1 : ℂ)).trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (Circle.norm_coe u.1))

theorem apm_t02a03_leftTubeNormalAngular_torusInverse
    (u : Circle × Circle) :
    apm_t02a03_leftTubeNormalAngular
      (apm_t02a03_leftTubeTorusInverse u) = u.2 := by
  apply Subtype.ext
  have hbre : -(1 : ℝ) ≤ (u.2 : ℂ).re := by
    have h := Complex.abs_re_le_norm (u.2 : ℂ)
    rw [Circle.norm_coe] at h
    exact (abs_le.mp h).1
  have hrpos : 0 < 1 + (1 / 8 : ℝ) * (u.2 : ℂ).re := by linarith
  have hplanar : apm_t02a03_leftTubePlanarComplex
      ⟨apm_t02a03_leftTubeTorusPoint u,
        apm_t02a03_leftTubeTorusPoint_mem_leftTube u⟩ =
      ((1 + (1 / 8 : ℝ) * (u.2 : ℂ).re : ℝ) : ℂ) * (u.1 : ℂ) := by
    apply Complex.ext <;>
      simp [apm_t02a03_leftTubePlanarComplex,
        apm_t02a03_leftTubeTorusPoint]
  have hnorm : ‖apm_t02a03_leftTubePlanarComplex
      ⟨apm_t02a03_leftTubeTorusPoint u,
        apm_t02a03_leftTubeTorusPoint_mem_leftTube u⟩‖ =
      1 + (1 / 8 : ℝ) * (u.2 : ℂ).re := by
    rw [hplanar]
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpos]
  change NormedSpace.normalize
      (apm_t02a03_leftTubeNormalComplex
        ⟨apm_t02a03_leftTubeTorusPoint u,
          apm_t02a03_leftTubeTorusPoint_mem_leftTube u⟩) = (u.2 : ℂ)
  rw [show apm_t02a03_leftTubeNormalComplex
      ⟨apm_t02a03_leftTubeTorusPoint u,
        apm_t02a03_leftTubeTorusPoint_mem_leftTube u⟩ =
      (1 / 8 : ℝ) • (u.2 : ℂ) by
    apply Complex.ext
    · simp [apm_t02a03_leftTubeNormalComplex]
      rw [hnorm]
      ring
    · simp [apm_t02a03_leftTubeNormalComplex,
        apm_t02a03_leftTubeTorusPoint]
      ]
  exact (NormedSpace.normalize_smul_of_pos
      (by norm_num : (0 : ℝ) < 1 / 8) (u.2 : ℂ)).trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (Circle.norm_coe u.2))

theorem apm_t02a03_leftTubeTorusCoordinates_torusInverse
    (u : Circle × Circle) :
    apm_t02a03_leftTubeTorusCoordinates
      (apm_t02a03_leftTubeTorusInverse u) = u := by
  apply Prod.ext
  · exact apm_t02a03_leftTubeAngular_torusInverse u
  · exact apm_t02a03_leftTubeNormalAngular_torusInverse u

theorem apm_t02a03_leftTubePlanar_norm_sub_one_le_corePlanarDistance
    (p : apm_t02a03_leftTubeSubtype) (t : ℝ) :
    |‖apm_t02a03_leftTubePlanarComplex p‖ - 1| ≤
      ‖apm_t02a03_leftTubePlanarComplex p -
        ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)‖ := by
  have hunit :
      ‖((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_def]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add]
    rw [show Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 by
      nlinarith [Real.sin_sq_add_cos_sq t]]
    norm_num
  simpa [hunit] using
    (abs_norm_sub_norm_le (apm_t02a03_leftTubePlanarComplex p)
      ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I))

theorem apm_t02a03_rightCore_zero :
    apm_t02a03_rightCore 0 = (0 : apm_t02a03_E3) := by
  ext i
  fin_cases i <;> simp [apm_t02a03_rightCore]

/-- The Euclidean origin is the common attachment point of the two core
circles in the frozen figure-eight geometry. -/
theorem apm_t02a03_origin_mem_both_cores :
    (0 : apm_t02a03_E3) ∈ Set.range apm_t02a03_leftCore ∩
      Set.range apm_t02a03_rightCore := by
  exact ⟨⟨0, apm_t02a03_leftCore_zero⟩,
    ⟨0, apm_t02a03_rightCore_zero⟩⟩

theorem apm_t02a03_origin_mem_both_tubes :
    (0 : apm_t02a03_E3) ∈ apm_t02a03_leftTube ∩ apm_t02a03_rightTube := by
  exact ⟨Metric.self_subset_cthickening _
      apm_t02a03_origin_mem_both_cores.1,
    Metric.self_subset_cthickening _
      apm_t02a03_origin_mem_both_cores.2⟩

/-- The two frozen core circles meet only at their common attachment point. -/
theorem apm_t02a03_core_ranges_intersection :
    Set.range apm_t02a03_leftCore ∩ Set.range apm_t02a03_rightCore =
      ({0} : Set apm_t02a03_E3) := by
  ext p
  constructor
  · rintro ⟨⟨t, rfl⟩, ⟨s, hts⟩⟩
    have hx := congrArg (fun q : apm_t02a03_E3 => q 0) hts
    simp [apm_t02a03_leftCore, apm_t02a03_rightCore] at hx
    have hcost : Real.cos t = 1 := by
      have ht := Real.cos_le_one t
      have hs := Real.cos_le_one s
      linarith
    have hsint : Real.sin t = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    simp only [Set.mem_singleton_iff]
    ext i
    fin_cases i <;>
      simp [apm_t02a03_leftCore, hcost, hsint]
  · intro hp
    have hp0 : p = 0 := Set.mem_singleton_iff.mp hp
    subst p
    exact apm_t02a03_origin_mem_both_cores

/-- Deleting the left core from the right core deletes exactly their common
attachment point. -/
theorem apm_t02a03_rightCore_diff_leftCore :
    Set.range apm_t02a03_rightCore \ Set.range apm_t02a03_leftCore =
      Set.range apm_t02a03_rightCore \ ({0} : Set apm_t02a03_E3) := by
  ext p
  constructor
  · rintro ⟨hpR, hpL⟩
    refine ⟨hpR, ?_⟩
    intro hp0
    apply hpL
    have hpI : p ∈ Set.range apm_t02a03_leftCore ∩
        Set.range apm_t02a03_rightCore := by
      rw [apm_t02a03_core_ranges_intersection]
      exact hp0
    exact hpI.1
  · rintro ⟨hpR, hp0⟩
    refine ⟨hpR, ?_⟩
    intro hpL
    apply hp0
    rw [← apm_t02a03_core_ranges_intersection]
    exact ⟨hpL, hpR⟩

/-- A point of the right core belongs to the frozen geometric complement
exactly when it is not the common origin. -/
theorem apm_t02a03_rightCore_mem_geometricY_iff (t : ℝ) :
    (apm_t02a03_rightCore t ∈ apm_t02a03_W ∧
      apm_t02a03_rightCore t ∉ Set.range apm_t02a03_leftCore) ↔
      apm_t02a03_rightCore t ≠ 0 := by
  have htR : apm_t02a03_rightCore t ∈ Set.range apm_t02a03_rightCore :=
    ⟨t, rfl⟩
  have htW : apm_t02a03_rightCore t ∈ apm_t02a03_W := by
    rw [apm_t02a03_W_eq_leftTube_union_rightTube]
    exact Set.mem_union_right _
      (Metric.self_subset_cthickening _ htR)
  constructor
  · rintro ⟨_, htL⟩ ht0
    apply htL
    rw [ht0]
    exact apm_t02a03_origin_mem_both_cores.1
  · intro ht0
    refine ⟨htW, ?_⟩
    intro htL
    apply ht0
    have htI : apm_t02a03_rightCore t ∈
        Set.range apm_t02a03_leftCore ∩ Set.range apm_t02a03_rightCore :=
      ⟨htL, htR⟩
    rw [apm_t02a03_core_ranges_intersection] at htI
    exact Set.mem_singleton_iff.mp htI

abbrev apm_t02a03_geometricY_probe :=
  {p : apm_t02a03_E3 // p ∈ apm_t02a03_W ∧
    p ∉ Set.range apm_t02a03_leftCore}

theorem apm_t02a03_continuous_rightCore :
    Continuous apm_t02a03_rightCore := by
  unfold apm_t02a03_rightCore
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The surviving right-core parametrization, with its codomain restricted to
the frozen geometric complement. -/
noncomputable def apm_t02a03_rightCoreSurvivorMap :
    C({t : ℝ // apm_t02a03_rightCore t ≠ 0},
      apm_t02a03_geometricY_probe) where
  toFun t := ⟨apm_t02a03_rightCore t,
    (apm_t02a03_rightCore_mem_geometricY_iff t).2 t.property⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      (apm_t02a03_continuous_rightCore.comp continuous_subtype_val) _

/-- A fixed point on the normal meridian above the deleted common origin. -/
noncomputable def apm_t02a03_meridianAnchor : apm_t02a03_E3 :=
  WithLp.toLp 2 ![0, 0, (1 / 8 : ℝ)]

theorem apm_t02a03_meridianAnchor_mem_geometricY :
    apm_t02a03_meridianAnchor ∈ apm_t02a03_W ∧
      apm_t02a03_meridianAnchor ∉ Set.range apm_t02a03_leftCore := by
  constructor
  · rw [apm_t02a03_W_eq_leftTube_union_rightTube]
    apply Set.mem_union_left
    apply Metric.mem_cthickening_of_dist_le apm_t02a03_meridianAnchor 0
      (1 / 4 : ℝ) (Set.range apm_t02a03_leftCore)
      apm_t02a03_origin_mem_both_cores.1
    rw [dist_zero_right]
    change ‖WithLp.toLp 2 ![0, 0, (1 / 8 : ℝ)]‖ ≤ (1 / 4 : ℝ)
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_succ]
  · rintro ⟨t, ht⟩
    have hz := congrArg (fun q : apm_t02a03_E3 => q 2) ht
    change (0 : ℝ) = 1 / 8 at hz
    norm_num at hz

noncomputable def apm_t02a03_meridian (t : ℝ) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![(1 / 8 : ℝ) * Real.cos t, 0,
    (1 / 8 : ℝ) * Real.sin t]

theorem apm_t02a03_meridian_mem_geometricY (t : ℝ) :
    apm_t02a03_meridian t ∈ apm_t02a03_W ∧
      apm_t02a03_meridian t ∉ Set.range apm_t02a03_leftCore := by
  constructor
  · rw [apm_t02a03_W_eq_leftTube_union_rightTube]
    apply Set.mem_union_left
    apply Metric.mem_cthickening_of_dist_le (apm_t02a03_meridian t) 0
      (1 / 4 : ℝ) (Set.range apm_t02a03_leftCore)
      apm_t02a03_origin_mem_both_cores.1
    rw [dist_zero_right]
    rw [EuclideanSpace.norm_eq]
    have hsq : ((1 / 8 : ℝ) * Real.cos t) ^ 2 +
        ((1 / 8 : ℝ) * Real.sin t) ^ 2 = 1 / 64 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    simp [apm_t02a03_meridian, Fin.sum_univ_succ]
    rw [show (8⁻¹ * Real.cos t) ^ 2 + (8⁻¹ * Real.sin t) ^ 2 =
        (1 / 64 : ℝ) by norm_num at hsq ⊢; exact hsq]
    norm_num
  · rintro ⟨s, hs⟩
    have hx := congrArg (fun q : apm_t02a03_E3 => q 0) hs
    have hy := congrArg (fun q : apm_t02a03_E3 => q 1) hs
    have hz := congrArg (fun q : apm_t02a03_E3 => q 2) hs
    simp [apm_t02a03_leftCore, apm_t02a03_meridian] at hx hy hz
    nlinarith [Real.sin_sq_add_cos_sq s, Real.sin_sq_add_cos_sq t,
      Real.neg_one_le_cos s, Real.cos_le_one s,
      Real.neg_one_le_cos t, Real.cos_le_one t]

noncomputable def apm_t02a03_meridianMap :
    C(ℝ, apm_t02a03_geometricY_probe) where
  toFun t := ⟨apm_t02a03_meridian t,
    apm_t02a03_meridian_mem_geometricY t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold apm_t02a03_meridian
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

noncomputable def apm_t02a03_circleMeridian (z : Circle) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![(1 / 8 : ℝ) * (z : ℂ).re, 0,
    (1 / 8 : ℝ) * (z : ℂ).im]

theorem apm_t02a03_circleMeridian_mem_geometricY (z : Circle) :
    apm_t02a03_circleMeridian z ∈ apm_t02a03_W ∧
      apm_t02a03_circleMeridian z ∉ Set.range apm_t02a03_leftCore := by
  have hzsq : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  constructor
  · rw [apm_t02a03_W_eq_leftTube_union_rightTube]
    apply Set.mem_union_left
    apply Metric.mem_cthickening_of_dist_le (apm_t02a03_circleMeridian z) 0
      (1 / 4 : ℝ) (Set.range apm_t02a03_leftCore)
      apm_t02a03_origin_mem_both_cores.1
    rw [dist_zero_right, EuclideanSpace.norm_eq]
    have hsq : ((1 / 8 : ℝ) * (z : ℂ).re) ^ 2 +
        ((1 / 8 : ℝ) * (z : ℂ).im) ^ 2 = 1 / 64 := by
      nlinarith
    simp [apm_t02a03_circleMeridian, Fin.sum_univ_succ]
    rw [show (8⁻¹ * (z : ℂ).re) ^ 2 + (8⁻¹ * (z : ℂ).im) ^ 2 =
        (1 / 64 : ℝ) by norm_num at hsq ⊢; exact hsq]
    norm_num
  · rintro ⟨s, hs⟩
    have hx := congrArg (fun q : apm_t02a03_E3 => q 0) hs
    have hy := congrArg (fun q : apm_t02a03_E3 => q 1) hs
    have hz := congrArg (fun q : apm_t02a03_E3 => q 2) hs
    simp [apm_t02a03_leftCore, apm_t02a03_circleMeridian] at hx hy hz
    have hcos : Real.cos s ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq s]
    have hre : (z : ℂ).re ^ 2 = 1 := by
      nlinarith
    nlinarith [sq_nonneg (Real.cos s - 1),
      sq_nonneg ((z : ℂ).re - 1), sq_nonneg ((z : ℂ).re + 1)]

noncomputable def apm_t02a03_circleMeridianMap :
    C(Circle, apm_t02a03_geometricY_probe) where
  toFun z := ⟨apm_t02a03_circleMeridian z,
    apm_t02a03_circleMeridian_mem_geometricY z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold apm_t02a03_circleMeridian
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

theorem apm_t02a03_circleMeridian_exp (t : ℝ) :
    apm_t02a03_circleMeridian (Circle.exp t) =
      apm_t02a03_meridian t := by
  ext i
  fin_cases i <;>
    simp [apm_t02a03_circleMeridian, apm_t02a03_meridian,
      Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]

theorem apm_t02a03_circleMeridian_quarterTurn :
    apm_t02a03_circleMeridian (Circle.exp (Real.pi / 2)) =
      apm_t02a03_meridianAnchor := by
  rw [apm_t02a03_circleMeridian_exp]
  ext i
  fin_cases i <;>
    simp [apm_t02a03_meridian, apm_t02a03_meridianAnchor]

noncomputable def apm_t02a03_attachmentCollarPoint
    (u : Set.Ico (0 : ℝ) 1) : apm_t02a03_E3 :=
  WithLp.toLp 2 ![0, 0, (1 - (u : ℝ)) / 8]

theorem apm_t02a03_attachmentCollarPoint_mem_geometricY
    (u : Set.Ico (0 : ℝ) 1) :
    apm_t02a03_attachmentCollarPoint u ∈ apm_t02a03_W ∧
      apm_t02a03_attachmentCollarPoint u ∉
        Set.range apm_t02a03_leftCore := by
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hu1 : (u : ℝ) < 1 := u.property.2
  constructor
  · rw [apm_t02a03_W_eq_leftTube_union_rightTube]
    apply Set.mem_union_left
    apply Metric.mem_cthickening_of_dist_le
      (apm_t02a03_attachmentCollarPoint u) 0 (1 / 4 : ℝ)
      (Set.range apm_t02a03_leftCore)
      apm_t02a03_origin_mem_both_cores.1
    rw [dist_zero_right, EuclideanSpace.norm_eq]
    simp [apm_t02a03_attachmentCollarPoint, Fin.sum_univ_succ]
    rw [Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ (1 - (u : ℝ)) / 8)]
    linarith
  · rintro ⟨s, hs⟩
    have hz := congrArg (fun q : apm_t02a03_E3 => q 2) hs
    simp [apm_t02a03_leftCore, apm_t02a03_attachmentCollarPoint] at hz
    linarith

noncomputable def apm_t02a03_attachmentCollarMap :
    C(Set.Ico (0 : ℝ) 1, apm_t02a03_geometricY_probe) where
  toFun u := ⟨apm_t02a03_attachmentCollarPoint u,
    apm_t02a03_attachmentCollarPoint_mem_geometricY u⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold apm_t02a03_attachmentCollarPoint
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

theorem apm_t02a03_attachmentCollarMap_zero :
    apm_t02a03_attachmentCollarMap ⟨0, by simp⟩ =
      ⟨apm_t02a03_meridianAnchor,
        apm_t02a03_meridianAnchor_mem_geometricY⟩ := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [apm_t02a03_attachmentCollarMap,
      apm_t02a03_attachmentCollarPoint, apm_t02a03_meridianAnchor]

noncomputable def apm_t02a03_attachmentCollarClosureMap :
    C(Set.Icc (0 : ℝ) 1, apm_t02a03_E3) where
  toFun u := WithLp.toLp 2 ![0, 0, (1 - (u : ℝ)) / 8]
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

theorem apm_t02a03_attachmentCollarClosureMap_zero :
    apm_t02a03_attachmentCollarClosureMap ⟨0, by simp⟩ =
      apm_t02a03_meridianAnchor := by
  ext i
  fin_cases i <;>
    simp [apm_t02a03_attachmentCollarClosureMap,
      apm_t02a03_meridianAnchor]

theorem apm_t02a03_attachmentCollarClosureMap_one :
    apm_t02a03_attachmentCollarClosureMap ⟨1, by simp⟩ = 0 := by
  ext i
  fin_cases i <;>
    simp [apm_t02a03_attachmentCollarClosureMap]

noncomputable def apm_t02a03_rightCoreAttachmentClosureMap :
    C(Set.Icc (0 : ℝ) 1, apm_t02a03_E3) where
  toFun t := apm_t02a03_rightCore (t : ℝ)
  continuous_toFun :=
    apm_t02a03_continuous_rightCore.comp continuous_subtype_val

theorem apm_t02a03_rightCoreAttachmentClosureMap_zero :
    apm_t02a03_rightCoreAttachmentClosureMap ⟨0, by simp⟩ = 0 := by
  exact apm_t02a03_rightCore_zero

theorem apm_t02a03_rightCoreAttachmentPoint_mem_geometricY
    (t : Set.Ioc (0 : ℝ) 1) :
    apm_t02a03_rightCore (t : ℝ) ∈ apm_t02a03_W ∧
      apm_t02a03_rightCore (t : ℝ) ∉
        Set.range apm_t02a03_leftCore := by
  apply (apm_t02a03_rightCore_mem_geometricY_iff (t : ℝ)).2
  intro ht
  have hx := congrArg (fun q : apm_t02a03_E3 => q 0) ht
  simp [apm_t02a03_rightCore] at hx
  have hx' : Real.cos (t : ℝ) = 1 := by linarith
  have htlt : (t : ℝ) < 2 * Real.pi := by
    nlinarith [t.property.2, Real.pi_gt_three]
  have ht0 := (Real.cos_eq_one_iff_of_lt_of_lt
    (x := (t : ℝ)) (by nlinarith [t.property.1, Real.pi_pos]) htlt).mp hx'
  exact (ne_of_gt t.property.1) ht0

noncomputable def apm_t02a03_rightCoreAttachmentMap :
    C(Set.Ioc (0 : ℝ) 1, apm_t02a03_geometricY_probe) where
  toFun t := ⟨apm_t02a03_rightCore (t : ℝ),
    apm_t02a03_rightCoreAttachmentPoint_mem_geometricY t⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      (apm_t02a03_continuous_rightCore.comp continuous_subtype_val) _

theorem apm_t02a03_rightCore_collar_deletedEndpoint :
    apm_t02a03_rightCoreAttachmentClosureMap ⟨0, by simp⟩ =
      apm_t02a03_attachmentCollarClosureMap ⟨1, by simp⟩ := by
  rw [apm_t02a03_rightCoreAttachmentClosureMap_zero,
    apm_t02a03_attachmentCollarClosureMap_one]

noncomputable def apm_t02a03_rightCoreLiftPoint
    (v : Set.Icc (0 : ℝ) 1 × Set.Ioc (0 : ℝ) 1) : apm_t02a03_E3 :=
  apm_t02a03_rightCore (v.2 : ℝ) +
    WithLp.toLp 2 ![0, 0, (v.1 : ℝ) / 8]

theorem apm_t02a03_rightCoreLiftPoint_mem_geometricY
    (v : Set.Icc (0 : ℝ) 1 × Set.Ioc (0 : ℝ) 1) :
    apm_t02a03_rightCoreLiftPoint v ∈ apm_t02a03_W ∧
      apm_t02a03_rightCoreLiftPoint v ∉
        Set.range apm_t02a03_leftCore := by
  constructor
  · rw [apm_t02a03_W_eq_leftTube_union_rightTube]
    apply Set.mem_union_right
    apply Metric.mem_cthickening_of_dist_le
      (apm_t02a03_rightCoreLiftPoint v)
      (apm_t02a03_rightCore (v.2 : ℝ)) (1 / 4 : ℝ)
      (Set.range apm_t02a03_rightCore) ⟨(v.2 : ℝ), rfl⟩
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [apm_t02a03_rightCoreLiftPoint, apm_t02a03_rightCore,
      Fin.sum_univ_succ]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
      (div_nonneg v.1.property.1 (by norm_num))]
    nlinarith [v.1.property.2]
  · intro hL
    rcases hL with ⟨u, hu⟩
    have hz := congrArg (fun q : apm_t02a03_E3 => q 2) hu
    simp [apm_t02a03_rightCoreLiftPoint, apm_t02a03_rightCore,
      apm_t02a03_leftCore] at hz
    have hs0 : (v.1 : ℝ) = 0 := by linarith
    have hp : apm_t02a03_rightCoreLiftPoint v =
        apm_t02a03_rightCore (v.2 : ℝ) := by
      ext i
      fin_cases i <;>
        simp [apm_t02a03_rightCoreLiftPoint, hs0]
    exact (apm_t02a03_rightCoreAttachmentPoint_mem_geometricY v.2).2
      ⟨u, hp ▸ hu⟩

noncomputable def apm_t02a03_rightCoreLiftHomotopyMap :
    C(Set.Icc (0 : ℝ) 1 × Set.Ioc (0 : ℝ) 1,
      apm_t02a03_geometricY_probe) where
  toFun v := ⟨apm_t02a03_rightCoreLiftPoint v,
    apm_t02a03_rightCoreLiftPoint_mem_geometricY v⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold apm_t02a03_rightCoreLiftPoint
    apply Continuous.add
    · exact apm_t02a03_continuous_rightCore.comp
        (continuous_subtype_val.comp continuous_snd)
    · apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop

theorem apm_t02a03_rightCoreLiftHomotopyMap_zero
    (t : Set.Ioc (0 : ℝ) 1) :
    apm_t02a03_rightCoreLiftHomotopyMap (⟨0, by simp⟩, t) =
      apm_t02a03_rightCoreAttachmentMap t := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [apm_t02a03_rightCoreLiftHomotopyMap,
      apm_t02a03_rightCoreLiftPoint,
      apm_t02a03_rightCoreAttachmentMap]

noncomputable def apm_t02a03_rightCoreLiftedMap :
    C(Set.Ioc (0 : ℝ) 1, apm_t02a03_geometricY_probe) where
  toFun t := apm_t02a03_rightCoreLiftHomotopyMap (⟨1, by simp⟩, t)
  continuous_toFun :=
    apm_t02a03_rightCoreLiftHomotopyMap.continuous.comp
      (continuous_const.prodMk continuous_id)

theorem apm_t02a03_rightCoreLiftHomotopyMap_one
    (t : Set.Ioc (0 : ℝ) 1) :
    apm_t02a03_rightCoreLiftHomotopyMap (⟨1, by simp⟩, t) =
      apm_t02a03_rightCoreLiftedMap t := rfl

noncomputable def apm_t02a03_rightCoreAnchorContractionPoint
    (v : Set.Icc (0 : ℝ) 1 × Set.Ioc (0 : ℝ) 1) : apm_t02a03_E3 :=
  apm_t02a03_rightCore ((1 - (v.1 : ℝ)) * (v.2 : ℝ)) +
    WithLp.toLp 2 ![0, 0, (1 / 8 : ℝ)]

theorem apm_t02a03_rightCoreAnchorContractionPoint_mem_geometricY
    (v : Set.Icc (0 : ℝ) 1 × Set.Ioc (0 : ℝ) 1) :
    apm_t02a03_rightCoreAnchorContractionPoint v ∈ apm_t02a03_W ∧
      apm_t02a03_rightCoreAnchorContractionPoint v ∉
        Set.range apm_t02a03_leftCore := by
  constructor
  · rw [apm_t02a03_W_eq_leftTube_union_rightTube]
    apply Set.mem_union_right
    apply Metric.mem_cthickening_of_dist_le
      (apm_t02a03_rightCoreAnchorContractionPoint v)
      (apm_t02a03_rightCore ((1 - (v.1 : ℝ)) * (v.2 : ℝ)))
      (1 / 4 : ℝ) (Set.range apm_t02a03_rightCore)
      ⟨(1 - (v.1 : ℝ)) * (v.2 : ℝ), rfl⟩
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [apm_t02a03_rightCoreAnchorContractionPoint,
      apm_t02a03_rightCore, Fin.sum_univ_succ]
    norm_num
  · rintro ⟨u, hu⟩
    have hz := congrArg (fun q : apm_t02a03_E3 => q 2) hu
    simp [apm_t02a03_rightCoreAnchorContractionPoint,
      apm_t02a03_rightCore, apm_t02a03_leftCore] at hz

noncomputable def apm_t02a03_rightCoreAnchorContractionMap :
    C(Set.Icc (0 : ℝ) 1 × Set.Ioc (0 : ℝ) 1,
      apm_t02a03_geometricY_probe) where
  toFun v := ⟨apm_t02a03_rightCoreAnchorContractionPoint v,
    apm_t02a03_rightCoreAnchorContractionPoint_mem_geometricY v⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold apm_t02a03_rightCoreAnchorContractionPoint
    apply Continuous.add
    · exact apm_t02a03_continuous_rightCore.comp (by fun_prop)
    · fun_prop

theorem apm_t02a03_rightCoreAnchorContractionMap_zero
    (t : Set.Ioc (0 : ℝ) 1) :
    apm_t02a03_rightCoreAnchorContractionMap (⟨0, by simp⟩, t) =
      apm_t02a03_rightCoreLiftedMap t := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [apm_t02a03_rightCoreAnchorContractionMap,
      apm_t02a03_rightCoreAnchorContractionPoint,
      apm_t02a03_rightCoreLiftedMap,
      apm_t02a03_rightCoreLiftHomotopyMap,
      apm_t02a03_rightCoreLiftPoint]

theorem apm_t02a03_rightCoreAnchorContractionMap_one
    (t : Set.Ioc (0 : ℝ) 1) :
    apm_t02a03_rightCoreAnchorContractionMap (⟨1, by simp⟩, t) =
      ⟨apm_t02a03_meridianAnchor,
        apm_t02a03_meridianAnchor_mem_geometricY⟩ := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [apm_t02a03_rightCoreAnchorContractionMap,
      apm_t02a03_rightCoreAnchorContractionPoint,
      apm_t02a03_rightCore, apm_t02a03_meridianAnchor]

theorem apm_t02a03_anchor_eq_circleMeridianMap_quarterTurn :
    (⟨apm_t02a03_meridianAnchor,
        apm_t02a03_meridianAnchor_mem_geometricY⟩ :
      apm_t02a03_geometricY_probe) =
      apm_t02a03_circleMeridianMap (Circle.exp (Real.pi / 2)) := by
  apply Subtype.ext
  exact apm_t02a03_circleMeridian_quarterTurn.symm

noncomputable def apm_t02a03_rightCoreLiftHomotopy :
    ContinuousMap.Homotopy apm_t02a03_rightCoreAttachmentMap
      apm_t02a03_rightCoreLiftedMap where
  toFun := apm_t02a03_rightCoreLiftHomotopyMap
  map_zero_left := apm_t02a03_rightCoreLiftHomotopyMap_zero
  map_one_left := apm_t02a03_rightCoreLiftHomotopyMap_one

noncomputable def apm_t02a03_rightCoreAnchorContractionHomotopy :
    ContinuousMap.Homotopy apm_t02a03_rightCoreLiftedMap
      (ContinuousMap.const _
        (apm_t02a03_circleMeridianMap (Circle.exp (Real.pi / 2)))) where
  toFun := apm_t02a03_rightCoreAnchorContractionMap
  map_zero_left := apm_t02a03_rightCoreAnchorContractionMap_zero
  map_one_left t :=
    (apm_t02a03_rightCoreAnchorContractionMap_one t).trans
      apm_t02a03_anchor_eq_circleMeridianMap_quarterTurn

noncomputable def apm_t02a03_rightCoreBasedAttachmentHomotopy :
    ContinuousMap.Homotopy apm_t02a03_rightCoreAttachmentMap
      (ContinuousMap.const _
        (apm_t02a03_circleMeridianMap (Circle.exp (Real.pi / 2)))) :=
  apm_t02a03_rightCoreLiftHomotopy.trans
    apm_t02a03_rightCoreAnchorContractionHomotopy

end ConstructionTargets.T02A03GeometricTubeCover
