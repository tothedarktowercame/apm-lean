import ConstructionTargets.CoefficientSubspaceUnionRestrictedSmallHomology
import ConstructionTargets.BooleanTwoCoverScaffold
import ConstructionTargets.SingularExcision

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRestrictedCoverImage

open Set
open SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold

variable {X : Type} [TopologicalSpace X]

/-- The restricted Boolean cover of `A ∪ B`, viewed back in `X`, has exactly
    the union-generated ambient range as its image. -/
theorem restrictedUnionCover_image (A B : Set X) :
    (coverSmallSSet (restrictedCover (A ∪ B) (booleanCover A B))).image
        (TopCat.toSSet.map (subspaceInclusion (A ∪ B))) =
      ambientSubspaceRange A ⊔ ambientSubspaceRange B := by
  rw [restrictedCoverSmallSSet_image, iSup_bool_eq]
  change (ambientSubspaceRange (A ∪ B) ⊓ ambientSubspaceRange A) ⊔
      (ambientSubspaceRange (A ∪ B) ⊓ ambientSubspaceRange B) = _
  rw [inf_eq_right.mpr (ambientSubspaceRange_mono Set.subset_union_left),
    inf_eq_right.mpr (ambientSubspaceRange_mono Set.subset_union_right)]

#print axioms restrictedUnionCover_image
end ConstructionTargets.CoefficientSubspaceUnionRestrictedCoverImage
