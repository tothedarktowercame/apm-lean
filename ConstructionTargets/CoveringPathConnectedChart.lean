import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocPathConnected

open Set Topology Bundle

noncomputable section

namespace ConstructionTargets.CoveringPathConnectedChart

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Over a locally path-connected base, every point has a path-connected open
neighborhood contained in the base set of a covering trivialization. -/
theorem IsCoveringMap.exists_pathConnected_trivialization
    [LocPathConnectedSpace B] {p : E → B} (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) (b : B) :
    ∃ (t : Trivialization (p ⁻¹' {b}) p) (V : Set B),
      b ∈ V ∧ IsOpen V ∧ IsPathConnected V ∧ V ⊆ t.baseSet := by
  letI : Nonempty (p ⁻¹' {b}) := by
    obtain ⟨e, he⟩ := hsurj b
    exact ⟨⟨e, he⟩⟩
  let t := (hp b).toTrivialization
  have hbase : t.baseSet ∈ nhds b :=
    t.open_baseSet.mem_nhds (IsEvenlyCovered.mem_toTrivialization_baseSet (hp b))
  obtain ⟨V, ⟨hVopen, hbV, hVpc⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis b).mem_iff.mp hbase
  exact ⟨t, V, hbV, hVopen, hVpc, hVsub⟩

/-- The chosen chart can be restricted so that its base set is exactly the
path-connected neighborhood. -/
theorem IsCoveringMap.exists_pathConnected_restrictedTrivialization
    [LocPathConnectedSpace B] {p : E → B} (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) (b : B) :
    ∃ (t : Trivialization (p ⁻¹' {b}) p),
      b ∈ t.baseSet ∧ IsPathConnected t.baseSet := by
  obtain ⟨t, V, hbV, hVopen, hVpc, hVsub⟩ :=
    ConstructionTargets.CoveringPathConnectedChart.IsCoveringMap.exists_pathConnected_trivialization
      hp hsurj b
  let tV := t.restrOpen V hVopen
  refine ⟨tV, ?_, ?_⟩
  · exact ⟨hVsub hbV, hbV⟩
  · simpa [tV, Bundle.Trivialization.restrOpen, inter_eq_right.mpr hVsub] using hVpc

#print axioms IsCoveringMap.exists_pathConnected_trivialization
#print axioms IsCoveringMap.exists_pathConnected_restrictedTrivialization

end ConstructionTargets.CoveringPathConnectedChart
