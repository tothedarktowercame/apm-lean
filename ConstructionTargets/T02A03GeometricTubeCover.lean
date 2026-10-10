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

end ConstructionTargets.T02A03GeometricTubeCover
