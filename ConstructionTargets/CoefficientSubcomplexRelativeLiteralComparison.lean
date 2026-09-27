import ConstructionTargets.CoefficientSubcomplexRelativeHomologySequence
import ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
import ConstructionTargets.CoefficientIntersectionRangeComparison
import ConstructionTargets.CoefficientCokernelComparison

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
open ConstructionTargets.CoefficientIntersectionRangeComparison
open ConstructionTargets.CoefficientCokernelComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev P (A : Set X) := ambientSubspaceRange A

theorem rangeRelative_square (A : Set X) :
    leftAmbient R (P A) ≫ 𝟙 _ =
      (ambientSubspaceRangeChainsIso R A).hom ≫
        CoefficientRelativeSmall.subspaceMap R A := by
  simpa using (ambientSubspaceRangeChainsIso_hom_comp_subspaceMap R A).symm

noncomputable def rangeRelativeCokernelMap (A : Set X) :
    cokernel (leftAmbient R (P A)) ⟶ CoefficientRelativeSmall.relativeChains R A :=
  cokernel.map _ _ (ambientSubspaceRangeChainsIso R A).hom (𝟙 _)
    (rangeRelative_square R A)

noncomputable def intersectionRangeChainsToLiteral (A B : Set X) :=
  (intersectionChainsIso R A B).symm ≪≫
    ambientSubspaceRangeChainsIso R (A ∩ B)

theorem intersectionRelative_square (A B : Set X) :
    intersectionAmbient R (P A) (P B) ≫ 𝟙 _ =
      (intersectionRangeChainsToLiteral R A B).hom ≫
        CoefficientRelativeSmall.subspaceMap R (A ∩ B) := by
  rw [Category.comp_id]
  dsimp [intersectionRangeChainsToLiteral]
  rw [Category.assoc, ambientSubspaceRangeChainsIso_hom_comp_subspaceMap]
  dsimp [intersectionChainsIso, intersectionAmbient]
  change (CoefficientAmbientSubspaceRangeCompatibility.chains R).map
      (ambientSubspaceRange A ⊓ ambientSubspaceRange B).ι =
    (CoefficientAmbientSubspaceRangeCompatibility.chains R).map
        (ambientIntersectionRangeIso A B).inv ≫
      (CoefficientAmbientSubspaceRangeCompatibility.chains R).map
        (ambientSubspaceRange (A ∩ B)).ι
  rw [← Functor.map_comp]
  rfl

noncomputable def intersectionRelativeCokernelMap (A B : Set X) :
    cokernel (intersectionAmbient R (P A) (P B)) ⟶
      CoefficientRelativeSmall.relativeChains R (A ∩ B) :=
  cokernel.map _ _ (intersectionRangeChainsToLiteral R A B).hom (𝟙 _)
    (intersectionRelative_square R A B)

#print axioms rangeRelative_square
#print axioms rangeRelativeCokernelMap
#print axioms intersectionRelative_square
#print axioms intersectionRelativeCokernelMap
end ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison
