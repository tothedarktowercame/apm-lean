import ConstructionTargets.CoefficientSubspaceUnionRestrictedOpenCover
import ConstructionTargets.CoefficientSmallComparison

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRestrictedSmallHomology

open CategoryTheory Set
open ConstructionTargets.CoefficientSubspaceUnionRestrictedOpenCover

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

noncomputable def unionCoverHomologyIso (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (CoefficientSmallPath.coverSmallChains R (unionCover A B)).homology n ≅
      (CoefficientH0.SingularChains R (TopCat.of (A ∪ B : Set X))).homology n :=
  CoefficientSmallComparison.homologyIso R (unionCover A B)
    (unionCover_open hA hB) (unionCover_covers A B) n

theorem unionCoverHomologyIso_hom (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (unionCoverHomologyIso R A B hA hB n).hom =
      HomologicalComplex.homologyMap
        (CoefficientSmallPath.coverSmallInclusion R (unionCover A B)) n := rfl

theorem unionCover_homologyMap_isIso (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (CoefficientSmallPath.coverSmallInclusion R (unionCover A B)) n) := by
  rw [← unionCoverHomologyIso_hom R A B hA hB n]
  infer_instance

#print axioms unionCoverHomologyIso
#print axioms unionCoverHomologyIso_hom
#print axioms unionCover_homologyMap_isIso
end ConstructionTargets.CoefficientSubspaceUnionRestrictedSmallHomology
