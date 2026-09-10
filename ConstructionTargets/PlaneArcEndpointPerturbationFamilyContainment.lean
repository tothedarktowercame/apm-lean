import ConstructionTargets.PlaneArcEndpointPerturbationContainment

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointPerturbationFamilyContainment
open PlaneArcEndpointPreservingPerturbation
open PlaneArcEndpointPerturbationContainment

abbrev Plane := ℝ × ℝ

theorem exists_common_radius {ι : Type} [Finite ι]
    (a : ι → ℝ → Plane) (U : ι → Set ℝ) (W : ι → Set Plane)
    (hIU : ∀ i, Icc (0 : ℝ) 1 ⊆ U i)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) (U i))
    (hW : ∀ i, IsOpen (W i))
    (hsub : ∀ i, a i '' Icc (0 : ℝ) 1 ⊆ W i) :
    ∃ e : ℝ, 0 < e ∧ ∀ (v : ι → Plane), (∀ i, ‖v i‖ < e) →
      ∀ i t, t ∈ Icc (0 : ℝ) 1 → perturb (a i) (v i) t ∈ W i := by
  classical
  letI := Fintype.ofFinite ι
  have hcont (i : ι) : ContinuousOn (a i) (Icc (0 : ℝ) 1) :=
    (ha i).continuousOn.mono (hIU i)
  obtain ⟨e, he, heW⟩ := PlaneArcContainedSmallTranslations.image_margin
    (fun i => a i '' Icc (0 : ℝ) 1) W
    (fun i => isCompact_Icc.image_of_continuousOn (hcont i)) hW hsub
  refine ⟨e, he, fun v hv i t ht => heW i ?_⟩
  exact perturb_mem_thickening (a i) (v i) (a i '' Icc (0 : ℝ) 1)
    (hv i) ht ⟨t, ht, rfl⟩

#print axioms exists_common_radius

end PlaneArcEndpointPerturbationFamilyContainment
