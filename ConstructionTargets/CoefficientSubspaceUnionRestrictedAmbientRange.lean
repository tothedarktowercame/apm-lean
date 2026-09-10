import ConstructionTargets.CoefficientSubspaceUnionRestrictedCoverImage

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRestrictedAmbientRange

open CategoryTheory Set
open SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.CoefficientSubspaceUnionRestrictedCoverImage

variable {X : Type} [TopologicalSpace X]

noncomputable def restrictedUnionAmbientMap (A B : Set X) :
    (coverSmallSSet (restrictedCover (A ∪ B) (booleanCover A B)) : SSet) ⟶
      TopCat.toSSet.obj (TopCat.of X) :=
  (coverSmallSSet (restrictedCover (A ∪ B) (booleanCover A B))).ι ≫
    TopCat.toSSet.map (subspaceInclusion (A ∪ B))

theorem restrictedUnionAmbientMap_range (A B : Set X) :
    SSet.Subcomplex.range (restrictedUnionAmbientMap A B) =
      ambientSubspaceRange A ⊔ ambientSubspaceRange B := by
  rw [restrictedUnionAmbientMap, SSet.Subcomplex.range_comp,
    show SSet.Subcomplex.range
        (coverSmallSSet (restrictedCover (A ∪ B) (booleanCover A B))).ι =
      coverSmallSSet (restrictedCover (A ∪ B) (booleanCover A B)) from
        Subfunctor.range_ι _]
  exact restrictedUnionCover_image A B

#print axioms restrictedUnionAmbientMap
#print axioms restrictedUnionAmbientMap_range
end ConstructionTargets.CoefficientSubspaceUnionRestrictedAmbientRange
