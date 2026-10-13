import Mathlib
import ConstructionTargets.ComplexProjectiveChartTargets

open scoped LinearAlgebra.Projectivization
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t98a04_C2 := EuclideanSpace ℂ (Fin 2)
abbrev apm_t98a04_R3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t98a04_R2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t98a04_S3 := Metric.sphere (0 : apm_t98a04_C2) 1
abbrev apm_t98a04_CP1 := Projectivization ℂ apm_t98a04_C2

local instance : Fact (Module.finrank ℝ apm_t98a04_C2 = 3 + 1) := ⟨by
  rw [← Module.finrank_mul_finrank ℝ ℂ apm_t98a04_C2,
    Complex.finrank_real_complex]
  simp [apm_t98a04_C2]⟩

noncomputable instance : TopologicalSpace apm_t98a04_CP1 :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance

lemma apm_t98a04_sphere_ne_zero (z : apm_t98a04_S3) : z.1 ≠ 0 := by
  intro hz
  have hdist : dist (z.1 : apm_t98a04_C2) 0 = 1 := by
    simpa [dist_comm] using z.2
  simp [hz] at hdist

def apm_t98a04_hopf (z : apm_t98a04_S3) : apm_t98a04_CP1 :=
  Projectivization.mk ℂ z.1 (apm_t98a04_sphere_ne_zero z)

def apm_t98a04_e0 : {z : apm_t98a04_C2 // z ≠ 0} :=
  ⟨WithLp.toLp 2 ![(1 : ℂ), 0], by
    intro h
    have h0 := congrArg (fun z : apm_t98a04_C2 ↦ z 0) h
    simpa using h0⟩

def apm_t98a04_p10 : apm_t98a04_CP1 :=
  Projectivization.mk' ℂ apm_t98a04_e0

def apm_t98a04_fiber (p : apm_t98a04_CP1) : Set apm_t98a04_S3 :=
  {z | apm_t98a04_hopf z = p}

def apm_t98a04_circleOrbit (z : apm_t98a04_S3) : Set apm_t98a04_S3 :=
  {w | ∃ u : Circle, w.1 = (u : ℂ) • z.1}

def apm_t98a04_IsSubmersion
    (f : apm_t98a04_S3 → apm_t98a04_CP1) : Prop :=
  ∃ targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1,
    let _ := targetCharts
    IsManifold (𝓘(ℝ, apm_t98a04_R2)) (⊤ : ℕ∞) apm_t98a04_CP1 ∧
    ContMDiff (𝓘(ℝ, apm_t98a04_R3)) (𝓘(ℝ, apm_t98a04_R2))
      (⊤ : ℕ∞) f ∧
    ∀ z : apm_t98a04_S3,
      Function.Surjective
        (mfderiv (𝓘(ℝ, apm_t98a04_R3)) (𝓘(ℝ, apm_t98a04_R2)) f z)

lemma apm_t98a04_continuous_hopf : Continuous apm_t98a04_hopf := by
  change Continuous
    (Projectivization.mk' ℂ ∘
      fun z : apm_t98a04_S3 ↦
        (⟨z.1, apm_t98a04_sphere_ne_zero z⟩ :
          {w : apm_t98a04_C2 // w ≠ 0}))
  exact continuous_coinduced_rng.comp
    (continuous_subtype_val.subtype_mk fun z ↦ apm_t98a04_sphere_ne_zero z)

/-- LIBRARY: construct the usual affine atlas on CP¹ and verify the Hopf map
is a smooth submersion from Mathlib's standard unit sphere. -/
theorem apm_t98a04_submersion_bridge :
    apm_t98a04_IsSubmersion apm_t98a04_hopf := by
  sorry

/-- Two unit representatives of one projective point differ by a unit scalar. -/
-- BEGIN SEAT AREA
theorem apm_t98a04_fiber_eq_circleOrbit
    (p : apm_t98a04_CP1) (z : apm_t98a04_S3)
    (hz : z ∈ apm_t98a04_fiber p) :
    apm_t98a04_fiber p = apm_t98a04_circleOrbit z := by
  ext w
  constructor
  · intro hw
    have hp : apm_t98a04_hopf w = apm_t98a04_hopf z := by
      exact hw.trans hz.symm
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' ℂ w.1 z.1
        (apm_t98a04_sphere_ne_zero w) (apm_t98a04_sphere_ne_zero z)).mp hp
    have hw_norm : ‖(w.1 : apm_t98a04_C2)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using w.2
    have hz_norm : ‖(z.1 : apm_t98a04_C2)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using z.2
    have ha_norm : ‖a‖ = 1 := by
      rw [← ha, norm_smul, hz_norm, mul_one] at hw_norm
      exact hw_norm
    let u : Circle := ⟨a, by
      exact mem_sphere_zero_iff_norm.mpr ha_norm⟩
    exact ⟨u, ha.symm⟩
  · rintro ⟨u, hu⟩
    have hp : apm_t98a04_hopf w = apm_t98a04_hopf z := by
      apply (Projectivization.mk_eq_mk_iff' ℂ w.1 z.1
        (apm_t98a04_sphere_ne_zero w) (apm_t98a04_sphere_ne_zero z)).mpr
      exact ⟨(u : ℂ), hu.symm⟩
    exact hp.trans hz
-- END SEAT AREA

/-- The fiber over [1:0] is exactly the coordinate circle. -/
theorem apm_t98a04_fiber_p10 :
    apm_t98a04_fiber apm_t98a04_p10 = {z | z.1 1 = 0} := by
  sorry

/-- Every Hopf fiber is homeomorphic to the unit circle. -/
theorem apm_t98a04_fiber_homeomorph_circle
    (p : apm_t98a04_CP1) :
    Nonempty (apm_t98a04_fiber p ≃ₜ Circle) := by
  sorry

/-- LIBRARY: the Hopf fibration has no continuous section. -/
theorem apm_t98a04_no_section_bridge :
    ¬∃ i : apm_t98a04_CP1 → apm_t98a04_S3,
      Continuous i ∧ ∀ p, apm_t98a04_hopf (i p) = p := by
  sorry

theorem apm_t98a04 :
    Continuous apm_t98a04_hopf ∧
    apm_t98a04_IsSubmersion apm_t98a04_hopf ∧
    apm_t98a04_fiber apm_t98a04_p10 = {z | z.1 1 = 0} ∧
    (∀ p : apm_t98a04_CP1,
      Nonempty (apm_t98a04_fiber p ≃ₜ Circle) ∧
      ∀ z ∈ apm_t98a04_fiber p,
        apm_t98a04_fiber p = apm_t98a04_circleOrbit z) ∧
    ¬∃ i : apm_t98a04_CP1 → apm_t98a04_S3,
      Continuous i ∧ ∀ p, apm_t98a04_hopf (i p) = p := by
  refine ⟨apm_t98a04_continuous_hopf, apm_t98a04_submersion_bridge,
    apm_t98a04_fiber_p10, ?_, apm_t98a04_no_section_bridge⟩
  intro p
  exact ⟨apm_t98a04_fiber_homeomorph_circle p,
    fun z hz ↦ apm_t98a04_fiber_eq_circleOrbit p z hz⟩

#print axioms apm_t98a04
