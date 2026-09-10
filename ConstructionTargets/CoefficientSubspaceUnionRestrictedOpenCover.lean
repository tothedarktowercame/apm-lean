import ConstructionTargets.CoefficientSubspaceUnionCoverSmallComparison

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRestrictedOpenCover

open Set

variable {X : Type} [TopologicalSpace X]

/-- The two subsets, restricted to their union as the ambient space. -/
def unionCover (A B : Set X) : Bool → Set (A ∪ B : Set X)
  | true => Subtype.val ⁻¹' A
  | false => Subtype.val ⁻¹' B

theorem unionCover_open {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    (b : Bool) : IsOpen (unionCover A B b) := by
  cases b
  · exact hB.preimage continuous_subtype_val
  · exact hA.preimage continuous_subtype_val

omit [TopologicalSpace X] in
theorem unionCover_covers (A B : Set X) :
    (Set.univ : Set (A ∪ B : Set X)) ⊆ ⋃ b, unionCover A B b := by
  intro x hx
  rcases x.2 with hxA | hxB
  · exact mem_iUnion.mpr ⟨true, hxA⟩
  · exact mem_iUnion.mpr ⟨false, hxB⟩

omit [TopologicalSpace X] in
theorem unionCover_iUnion (A B : Set X) :
    ⋃ b, unionCover A B b = Set.univ :=
  Set.eq_univ_of_univ_subset (unionCover_covers A B)

#print axioms unionCover_open
#print axioms unionCover_covers
#print axioms unionCover_iUnion
end ConstructionTargets.CoefficientSubspaceUnionRestrictedOpenCover
