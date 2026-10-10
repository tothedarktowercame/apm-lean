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

end ConstructionTargets.T02A03GeometricTubeCover
