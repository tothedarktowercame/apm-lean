import Mathlib.Topology.Connected.PathConnected

open Set

noncomputable section

namespace ConstructionTargets.PreconnectedClopenSheet

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous image of a preconnected space cannot cross the boundary of
a clopen subset: it lies wholly inside or wholly outside. -/
theorem range_subset_or_disjoint_of_isClopen [PreconnectedSpace X]
    {f : X → Y} (hf : Continuous f) {C : Set Y} (hC : IsClopen C) :
    Set.range f ⊆ C ∨ Disjoint (Set.range f) C := by
  have hpre : IsClopen (f ⁻¹' C) := hC.preimage hf
  rcases isClopen_iff.mp hpre with hempty | huniv
  · right
    rw [Set.disjoint_left]
    rintro y ⟨x, rfl⟩ hfx
    exact (Set.ext_iff.mp hempty x).mp hfx
  · left
    rintro y ⟨x, rfl⟩
    exact (Set.ext_iff.mp huniv x).mpr (Set.mem_univ x)

/-- A path-connected covering-chart base therefore selects an entire sheet
or no point of that sheet when intersected with a clopen component. -/
theorem range_subset_or_disjoint_of_isClopen_pathConnected
    [PathConnectedSpace X] {f : X → Y} (hf : Continuous f)
    {C : Set Y} (hC : IsClopen C) :
    Set.range f ⊆ C ∨ Disjoint (Set.range f) C :=
  range_subset_or_disjoint_of_isClopen hf hC

#print axioms range_subset_or_disjoint_of_isClopen
#print axioms range_subset_or_disjoint_of_isClopen_pathConnected

end ConstructionTargets.PreconnectedClopenSheet
