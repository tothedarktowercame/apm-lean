import ConstructionTargets.CoefficientCompactComplementTransportedArrows
import ConstructionTargets.CoefficientRadialPair

noncomputable section
namespace ConstructionTargets.CoefficientCompactSupportRestrictionMaps

open CategoryTheory CategoryTheory.Limits Set
open ConstructionTargets.CoefficientRadialPair

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev relative (A : Set X) :=
  CoefficientRelativeSmall.relativeChains R A

omit [TopologicalSpace X] in
theorem unionComplement_subset_leftComplement (K L : Set X) :
    (K ∪ L)ᶜ ⊆ Kᶜ := by
  intro x hx hK
  exact hx (Or.inl hK)

omit [TopologicalSpace X] in
theorem unionComplement_subset_rightComplement (K L : Set X) :
    (K ∪ L)ᶜ ⊆ Lᶜ := by
  intro x hx hL
  exact hx (Or.inr hL)

noncomputable def restrictLeft (K L : Set X) :
    relative R (K ∪ L)ᶜ ⟶ relative R Kᶜ :=
  pairMap R (K ∪ L)ᶜ Kᶜ (ContinuousMap.id X)
    (unionComplement_subset_leftComplement K L)

noncomputable def restrictRight (K L : Set X) :
    relative R (K ∪ L)ᶜ ⟶ relative R Lᶜ :=
  pairMap R (K ∪ L)ᶜ Lᶜ (ContinuousMap.id X)
    (unionComplement_subset_rightComplement K L)

noncomputable def restrictPieces (K L : Set X) (n : ℕ) :
    (relative R (K ∪ L)ᶜ).homology n ⟶
      (relative R Kᶜ).homology n ⊞ (relative R Lᶜ).homology n :=
  biprod.lift
    (HomologicalComplex.homologyMap (restrictLeft R K L) n)
    (HomologicalComplex.homologyMap (restrictRight R K L) n)

theorem restrictPieces_fst (K L : Set X) (n : ℕ) :
    restrictPieces R K L n ≫ biprod.fst =
      HomologicalComplex.homologyMap (restrictLeft R K L) n := by
  exact biprod.lift_fst _ _

theorem restrictPieces_snd (K L : Set X) (n : ℕ) :
    restrictPieces R K L n ≫ biprod.snd =
      HomologicalComplex.homologyMap (restrictRight R K L) n := by
  exact biprod.lift_snd _ _

#print axioms unionComplement_subset_leftComplement
#print axioms unionComplement_subset_rightComplement
#print axioms restrictLeft
#print axioms restrictRight
#print axioms restrictPieces
#print axioms restrictPieces_fst
#print axioms restrictPieces_snd
end ConstructionTargets.CoefficientCompactSupportRestrictionMaps
