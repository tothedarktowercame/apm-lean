import ConstructionTargets.CoefficientCompactSupportRelativeShortComplex
import ConstructionTargets.SingularExcision

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRangeInclusion

open CategoryTheory Set
open ConstructionTargets.SingularExcision

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)

omit [TopologicalSpace X] in
theorem left_subset_union (A B : Set X) : A ⊆ A ∪ B := Set.subset_union_left

omit [TopologicalSpace X] in
theorem right_subset_union (A B : Set X) : B ⊆ A ∪ B := Set.subset_union_right

noncomputable def unionRangeInclusion (A B : Set X) :
    ((ambientSubspaceRange A ⊔ ambientSubspaceRange B :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) ⟶
      (ambientSubspaceRange (A ∪ B) : SSet) :=
  SSet.Subcomplex.homOfLE (sup_le
    (ambientSubspaceRange_mono (left_subset_union A B))
    (ambientSubspaceRange_mono (right_subset_union A B)))

noncomputable def unionRangeChainsInclusion (A B : Set X) :
    (chains R).obj ((ambientSubspaceRange A ⊔ ambientSubspaceRange B :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) ⟶
      (chains R).obj (ambientSubspaceRange (A ∪ B) : SSet) :=
  (chains R).map (unionRangeInclusion A B)

theorem unionRangeInclusion_comp_ambient (A B : Set X) :
    unionRangeInclusion A B ≫ (ambientSubspaceRange (A ∪ B)).ι =
      (ambientSubspaceRange A ⊔ ambientSubspaceRange B).ι := rfl

theorem unionRangeChainsInclusion_comp_ambient (A B : Set X) :
    unionRangeChainsInclusion R A B ≫
      (chains R).map (ambientSubspaceRange (A ∪ B)).ι =
      (chains R).map (ambientSubspaceRange A ⊔ ambientSubspaceRange B).ι := by
  change (chains R).map (unionRangeInclusion A B) ≫
      (chains R).map (ambientSubspaceRange (A ∪ B)).ι = _
  rw [← Functor.map_comp, unionRangeInclusion_comp_ambient]

#print axioms unionRangeInclusion
#print axioms unionRangeChainsInclusion
#print axioms unionRangeInclusion_comp_ambient
#print axioms unionRangeChainsInclusion_comp_ambient
end ConstructionTargets.CoefficientSubspaceUnionRangeInclusion
