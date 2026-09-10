import ConstructionTargets.CoefficientSubspaceUnionRangeFactorization
import ConstructionTargets.CoefficientSubspaceUnionRestrictedSmallHomology

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.CoefficientSubspaceUnionRangeInclusion
open ConstructionTargets.CoefficientSubspaceUnionRestrictedRangeIso
open ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
open ConstructionTargets.CoefficientSubspaceUnionRestrictedOpenCover
open ConstructionTargets.CoefficientSubspaceUnionRestrictedSmallHomology
open ConstructionTargets.CoefficientSubspaceUnionRangeFactorization

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

theorem unionRange_homologyMap_isIso (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (unionRangeChainsInclusion R A B) n) := by
  haveI hsmall : IsIso (HomologicalComplex.homologyMap
      (CoefficientSmallPath.coverSmallInclusion R
        (restrictedCover (A ∪ B) (booleanCover A B))) n) := by
    rw [← unionCover_eq_restrictedCover A B]
    exact unionCover_homologyMap_isIso R A B hA hB n
  rw [unionRangeChainsInclusion_factorization R A B,
    HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  infer_instance

#print axioms unionRange_homologyMap_isIso
end ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence
