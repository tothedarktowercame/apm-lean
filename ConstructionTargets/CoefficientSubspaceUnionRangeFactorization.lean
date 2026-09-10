import ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
import ConstructionTargets.CoefficientSubspaceUnionRestrictedSmallHomology

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRangeFactorization

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.CoefficientSubspaceUnionRangeInclusion
open ConstructionTargets.CoefficientSubspaceUnionRestrictedAmbientRange
open ConstructionTargets.CoefficientSubspaceUnionRestrictedRangeIso
open ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
open ConstructionTargets.CoefficientSubspaceUnionRestrictedOpenCover

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

theorem unionCover_eq_restrictedCover (A B : Set X) :
    unionCover A B = restrictedCover (A ∪ B) (booleanCover A B) := by
  funext b
  cases b <;> rfl

theorem unionRangeChainsInclusion_factorization (A B : Set X) :
    unionRangeChainsInclusion R A B =
      (restrictedUnionRangeChainsIso R A B).inv ≫
        CoefficientSmallPath.coverSmallInclusion R
          (restrictedCover (A ∪ B) (booleanCover A B)) ≫
          (ambientSubspaceRangeChainsIso R (A ∪ B)).inv := by
  haveI : Mono (CoefficientRelativeSmall.subspaceMap R (A ∪ B)) :=
    CoefficientRelativeSmall.subspaceMap_mono R (A ∪ B)
  apply (cancel_mono (ambientSubspaceRangeChainsIso R (A ∪ B)).hom).1
  simp
  apply (cancel_mono (CoefficientRelativeSmall.subspaceMap R (A ∪ B))).1
  rw [Category.assoc,
    ambientSubspaceRangeChainsIso_hom_comp_subspaceMap R (A ∪ B)]
  change unionRangeChainsInclusion R A B ≫
      (CoefficientSubspaceUnionRangeInclusion.chains R).map
        (ambientSubspaceRange (A ∪ B)).ι = _
  rw [unionRangeChainsInclusion_comp_ambient]
  rw [Category.assoc]
  have hdirect :
      CoefficientSmallPath.coverSmallInclusion R
          (restrictedCover (A ∪ B) (booleanCover A B)) ≫
        CoefficientRelativeSmall.subspaceMap R (A ∪ B) =
      (CoefficientSubspaceUnionRangeInclusion.chains R).map
        (restrictedUnionAmbientMap A B) := by
    change (CoefficientSubspaceUnionRangeInclusion.chains R).map _ ≫
      (CoefficientSubspaceUnionRangeInclusion.chains R).map _ = _
    rw [← Functor.map_comp]
    rfl
  rw [hdirect]
  rw [← restrictedUnionRangeChainsIso_hom_comp_ambient R A B]
  simp

#print axioms unionCover_eq_restrictedCover
#print axioms unionRangeChainsInclusion_factorization
end ConstructionTargets.CoefficientSubspaceUnionRangeFactorization
