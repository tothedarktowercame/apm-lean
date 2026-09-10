import ConstructionTargets.CoefficientSubspaceUnionRangeInclusion
import ConstructionTargets.BooleanTwoCoverScaffold
import ConstructionTargets.CoefficientSmallPath

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionCoverSmallComparison

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.CoefficientSubspaceUnionRangeInclusion

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

noncomputable def unionRangeCoverSmallIso (A B : Set X) :
    (chains R).obj ((ambientSubspaceRange A ⊔ ambientSubspaceRange B :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) ≅
      CoefficientSmallPath.coverSmallChains R (booleanCover A B) :=
  (chains R).mapIso (smallSSetIsoCoverSmall A B)

theorem unionRangeCoverSmallIso_hom_comp_ambient (A B : Set X) :
    (unionRangeCoverSmallIso R A B).hom ≫
        CoefficientSmallPath.coverSmallInclusion R (booleanCover A B) =
      unionRangeChainsInclusion R A B ≫
        (chains R).map (ambientSubspaceRange (A ∪ B)).ι := by
  rw [unionRangeChainsInclusion_comp_ambient]
  change (chains R).map (smallSSetIsoCoverSmall A B).hom ≫
      (chains R).map (coverSmallSSet (booleanCover A B)).ι =
    (chains R).map (ambientSubspaceRange A ⊔ ambientSubspaceRange B).ι
  rw [← Functor.map_comp, smallSSetIsoCoverSmall_hom_comp_ambient]
  rfl

#print axioms unionRangeCoverSmallIso
#print axioms unionRangeCoverSmallIso_hom_comp_ambient
end ConstructionTargets.CoefficientSubspaceUnionCoverSmallComparison
