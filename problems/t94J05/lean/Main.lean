import Mathlib
import ConstructionTargets.FixedTargetChartDimensionDropNullity
import ConstructionTargets.FixedChartNullForcesNonsurjectivity

/-!
# APM t94J05 — smooth maps from the torus to the three-sphere

## Statement repairs

The former opaque smoothness predicate is replaced by Mathlib's native
`ContMDiff` predicate, using the product of the analytic `Circle` models
`(𝓡 1).prod (𝓡 1)` and the analytic three-sphere model `𝓡 3`.

## Encoding questions

The source torus is the actual product of two circles and the target is the
unit `3`-sphere in Euclidean `ℝ⁴`. Homotopy is Mathlib's native
continuous-map homotopy.
-/

open scoped ContDiff Manifold

abbrev apm_t94J05_Torus := Circle × Circle
abbrev apm_t94J05_R4 := EuclideanSpace ℝ (Fin 4)
abbrev apm_t94J05_S3 := Metric.sphere (0 : apm_t94J05_R4) 1

/-- The point `(0,0,0,1)` on the unit three-sphere. -/
noncomputable def apm_t94J05_northPole : apm_t94J05_S3 :=
  ⟨EuclideanSpace.single (3 : Fin 4) 1, by simp⟩

/-- A nonsurjective map to the sphere factors through the complement of a
missed point. This is the sphere-specialized form of the bridge proved in
problem `t01A01`. -/
lemma apm_t94J05_factor_through_complement
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (hnot_surj : ¬Function.Surjective f) :
    ∃ q : apm_t94J05_S3,
      ∃ g : C(apm_t94J05_Torus, {y : apm_t94J05_S3 // y ≠ q}),
        ∀ x, (g x : apm_t94J05_S3) = f x := by
  obtain ⟨q, hq⟩ : ∃ q : apm_t94J05_S3, ∀ x, f x ≠ q := by
    simpa [Function.Surjective] using hnot_surj
  refine ⟨q, ⟨fun x ↦ ⟨f x, hq x⟩, f.continuous.subtype_mk _⟩, ?_⟩
  intro x
  rfl

/-- A null-homotopy of the complement-valued factor descends along the
subtype inclusion. -/
lemma apm_t94J05_nullhomotopic_of_factor
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (q : apm_t94J05_S3)
    (g : C(apm_t94J05_Torus, {y : apm_t94J05_S3 // y ≠ q}))
    (hfg : ∀ x, (g x : apm_t94J05_S3) = f x)
    (p : {y : apm_t94J05_S3 // y ≠ q})
    (hg : ContinuousMap.Homotopic g (ContinuousMap.const _ p)) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus (p : apm_t94J05_S3)) := by
  let inclusion : C({y : apm_t94J05_S3 // y ≠ q}, apm_t94J05_S3) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hcomp := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl inclusion) hg
  have hleft : inclusion.comp g = f := by
    apply ContinuousMap.ext
    intro x
    exact hfg x
  simpa [hleft, inclusion] using hcomp

/-- On the path-connected three-sphere, the endpoint of a null-homotopy can
always be moved to the fixed north pole used by the theorem statement. -/
lemma apm_t94J05_nullhomotopic_to_northPole
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (p : apm_t94J05_S3)
    (hf : ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus p)) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole) := by
  have hs : IsPathConnected (Metric.sphere (0 : apm_t94J05_R4) 1) :=
    isPathConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  letI : PathConnectedSpace apm_t94J05_S3 :=
    isPathConnected_iff_pathConnectedSpace.mp hs
  have hp : Joined p apm_t94J05_northPole := PathConnectedSpace.joined _ _
  exact hf.trans (ContinuousMap.homotopic_const_iff.mpr hp)

/-- The complement of any point of the unit sphere is contractible, obtained
by transporting the vector-space contraction through stereographic
projection. -/
lemma apm_t94J05_contractibleSpace_complement (q : apm_t94J05_S3) :
    ContractibleSpace {y : apm_t94J05_S3 // y ≠ q} := by
  let hs := stereographic (norm_eq_of_mem_sphere q)
  have hsource : ({y : apm_t94J05_S3 | y ≠ q} : Set apm_t94J05_S3) = hs.source := by
    ext y
    simp [hs]
  have htarget : hs.target = Set.univ := stereographic_target _
  let eSource : {y : apm_t94J05_S3 // y ≠ q} ≃ₜ hs.source :=
    Homeomorph.setCongr hsource
  let eTarget : hs.target ≃ₜ (ℝ ∙ (q : apm_t94J05_R4))ᗮ :=
    (Homeomorph.setCongr htarget).trans (Homeomorph.Set.univ _)
  let e : {y : apm_t94J05_S3 // y ≠ q} ≃ₜ
      (ℝ ∙ (q : apm_t94J05_R4))ᗮ :=
    eSource.trans (hs.toHomeomorphSourceTarget.trans eTarget)
  exact e.contractibleSpace

/-- Every nonsurjective torus map is null-homotopic to the fixed north pole. -/
lemma apm_t94J05_nullhomotopic_of_not_surjective
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (hf : ¬ Function.Surjective f) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole) := by
  rcases apm_t94J05_factor_through_complement f hf with ⟨q, g, hfg⟩
  letI : ContractibleSpace {y : apm_t94J05_S3 // y ≠ q} :=
    apm_t94J05_contractibleSpace_complement q
  have hg0 : g.Nullhomotopic := by
    simpa using (id_nullhomotopic {y : apm_t94J05_S3 // y ≠ q}).comp_left g
  rcases hg0 with ⟨p, hg⟩
  exact apm_t94J05_nullhomotopic_to_northPole f p
    (apm_t94J05_nullhomotopic_of_factor f q g hfg p hg)

theorem apm_t94j05
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (hf : ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡 3) (⊤ : ℕ∞) f) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole) := by
  have hf_one : ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡 3) 1 f :=
    hf.of_le (by simp)
  have hdim :
      Module.finrank ℝ
          (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) := MeasureTheory.volume
  have hnull :=
    ConstructionTargets.FixedTargetChartDimensionDropNullity.fixed_extChartAt_range_inter_source_null
        ((𝓡 1).prod (𝓡 1)) (𝓡 3) f hf_one hdim μ apm_t94J05_northPole
  have hnot :=
    ConstructionTargets.FixedChartNullForcesNonsurjectivity.not_surjective_of_fixedChart_coordinateNull
        (𝓡 3) μ f apm_t94J05_northPole hnull
  exact apm_t94J05_nullhomotopic_of_not_surjective f hnot
