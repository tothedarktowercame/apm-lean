import ConstructionTargets.CoefficientCompactSupportPiecesToIntersection
import ConstructionTargets.CoefficientPairNaturality

noncomputable section
namespace ConstructionTargets.CoefficientCompactSupportRelativeArrowComplex

open CategoryTheory CategoryTheory.Limits Set
open ConstructionTargets.CoefficientRadialPair
open ConstructionTargets.CoefficientPairNaturality
open ConstructionTargets.CoefficientCompactSupportRestrictionMaps
open ConstructionTargets.CoefficientCompactSupportPiecesToIntersection

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

omit [TopologicalSpace X] in
theorem unionComplement_subset_intersectionComplement (K L : Set X) :
    (K ∪ L)ᶜ ⊆ (K ∩ L)ᶜ := by
  intro x hx hKL
  exact hx (Or.inl hKL.1)

noncomputable def directExtend (K L : Set X) :
    relative R (K ∪ L)ᶜ ⟶ relative R (K ∩ L)ᶜ :=
  pairMap R (K ∪ L)ᶜ (K ∩ L)ᶜ (ContinuousMap.id X)
    (unionComplement_subset_intersectionComplement K L)

theorem restrictLeft_extendLeft (K L : Set X) :
    restrictLeft R K L ≫ extendLeft R K L = directExtend R K L := by
  simpa [restrictLeft, extendLeft, directExtend] using
    (pair_comp R (K ∪ L)ᶜ Kᶜ (K ∩ L)ᶜ (ContinuousMap.id X)
      (ContinuousMap.id X) (unionComplement_subset_leftComplement K L)
      (leftComplement_subset_intersectionComplement K L)).symm

theorem restrictRight_extendRight (K L : Set X) :
    restrictRight R K L ≫ extendRight R K L = directExtend R K L := by
  simpa [restrictRight, extendRight, directExtend] using
    (pair_comp R (K ∪ L)ᶜ Lᶜ (K ∩ L)ᶜ (ContinuousMap.id X)
      (ContinuousMap.id X) (unionComplement_subset_rightComplement K L)
      (rightComplement_subset_intersectionComplement K L)).symm

noncomputable def restrictPiecesChain (K L : Set X) :
    relative R (K ∪ L)ᶜ ⟶ relative R Kᶜ ⊞ relative R Lᶜ :=
  biprod.lift (restrictLeft R K L) (restrictRight R K L)

theorem relative_arrows_zero (K L : Set X) :
    restrictPiecesChain R K L ≫ piecesToIntersection R K L = 0 := by
  simp only [restrictPiecesChain, piecesToIntersection, biprod.lift_desc, Preadditive.comp_neg,
    restrictLeft_extendLeft, restrictRight_extendRight, add_neg_cancel]

#print axioms unionComplement_subset_intersectionComplement
#print axioms directExtend
#print axioms restrictLeft_extendLeft
#print axioms restrictRight_extendRight
#print axioms restrictPiecesChain
#print axioms relative_arrows_zero
end ConstructionTargets.CoefficientCompactSupportRelativeArrowComplex
