import ConstructionTargets.CoefficientCompactSupportRestrictionMaps

noncomputable section
namespace ConstructionTargets.CoefficientCompactSupportPiecesToIntersection

open CategoryTheory CategoryTheory.Limits Set
open ConstructionTargets.CoefficientRadialPair
open ConstructionTargets.CoefficientCompactSupportRestrictionMaps

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

omit [TopologicalSpace X] in
theorem leftComplement_subset_intersectionComplement (K L : Set X) :
    Kᶜ ⊆ (K ∩ L)ᶜ := by
  intro x hx hKL
  exact hx hKL.1

omit [TopologicalSpace X] in
theorem rightComplement_subset_intersectionComplement (K L : Set X) :
    Lᶜ ⊆ (K ∩ L)ᶜ := by
  intro x hx hKL
  exact hx hKL.2

noncomputable def extendLeft (K L : Set X) :
    relative R Kᶜ ⟶ relative R (K ∩ L)ᶜ :=
  pairMap R Kᶜ (K ∩ L)ᶜ (ContinuousMap.id X)
    (leftComplement_subset_intersectionComplement K L)

noncomputable def extendRight (K L : Set X) :
    relative R Lᶜ ⟶ relative R (K ∩ L)ᶜ :=
  pairMap R Lᶜ (K ∩ L)ᶜ (ContinuousMap.id X)
    (rightComplement_subset_intersectionComplement K L)

noncomputable def piecesToIntersection (K L : Set X) :
    relative R Kᶜ ⊞ relative R Lᶜ ⟶ relative R (K ∩ L)ᶜ :=
  biprod.desc (extendLeft R K L) (-extendRight R K L)

noncomputable def piecesToIntersectionHomology (K L : Set X) (n : ℕ) :
    (relative R Kᶜ).homology n ⊞ (relative R Lᶜ).homology n ⟶
      (relative R (K ∩ L)ᶜ).homology n :=
  biprod.desc
    (HomologicalComplex.homologyMap (extendLeft R K L) n)
    (-HomologicalComplex.homologyMap (extendRight R K L) n)

#print axioms leftComplement_subset_intersectionComplement
#print axioms rightComplement_subset_intersectionComplement
#print axioms extendLeft
#print axioms extendRight
#print axioms piecesToIntersection
#print axioms piecesToIntersectionHomology
end ConstructionTargets.CoefficientCompactSupportPiecesToIntersection
