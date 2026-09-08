import ConstructionTargets.SardProjectedChartTargetFiberSliceContainment

open Set

namespace SardOpenChartSourceNeighborhoodRefinementProbe

/-- An open local equality can be refined inside the source of an open partial
homeomorphism while retaining the base point and the equality. -/
theorem exists_open_subset_chartSource_with_inter_eq
    {E Z : Type*} [TopologicalSpace E] [TopologicalSpace Z]
    (e : OpenPartialHomeomorph E Z) (x : E) (U A B : Set E)
    (hU : IsOpen U) (hxU : x ∈ U) (hxe : x ∈ e.source)
    (hEq : U ∩ A = U ∩ B) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ e.source ∧ V ∩ A = V ∩ B := by
  refine ⟨U ∩ e.source, hU.inter e.open_source, ⟨hxU, hxe⟩, inter_subset_right, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyU, hys⟩, hyA⟩
    have : y ∈ U ∩ B := hEq ▸ ⟨hyU, hyA⟩
    exact ⟨⟨hyU, hys⟩, this.2⟩
  · rintro ⟨⟨hyU, hys⟩, hyB⟩
    have : y ∈ U ∩ A := hEq.symm ▸ ⟨hyU, hyB⟩
    exact ⟨⟨hyU, hys⟩, this.2⟩

#print axioms exists_open_subset_chartSource_with_inter_eq

end SardOpenChartSourceNeighborhoodRefinementProbe
