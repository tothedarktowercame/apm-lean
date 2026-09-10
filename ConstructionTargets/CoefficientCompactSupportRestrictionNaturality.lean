import ConstructionTargets.CoefficientCompactSupportRestrictionMaps
import ConstructionTargets.CoefficientPairNaturality

noncomputable section
namespace ConstructionTargets.CoefficientCompactSupportRestrictionNaturality

open CategoryTheory Set
open ConstructionTargets.CoefficientRadialPair
open ConstructionTargets.CoefficientPairSequence
open ConstructionTargets.CoefficientPairNaturality
open ConstructionTargets.CoefficientCompactSupportRestrictionMaps

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

theorem restrictLeft_connecting (K L : Set X) (n : ℕ) :
    connecting R (K ∪ L)ᶜ n ≫
        HomologicalComplex.homologyMap
          (subMap R (K ∪ L)ᶜ Kᶜ (ContinuousMap.id X)
            (unionComplement_subset_leftComplement K L)) n =
      HomologicalComplex.homologyMap (restrictLeft R K L) (n + 1) ≫
        connecting R Kᶜ n := by
  exact connecting_naturality R (K ∪ L)ᶜ Kᶜ (ContinuousMap.id X)
    (unionComplement_subset_leftComplement K L) n

theorem restrictRight_connecting (K L : Set X) (n : ℕ) :
    connecting R (K ∪ L)ᶜ n ≫
        HomologicalComplex.homologyMap
          (subMap R (K ∪ L)ᶜ Lᶜ (ContinuousMap.id X)
            (unionComplement_subset_rightComplement K L)) n =
      HomologicalComplex.homologyMap (restrictRight R K L) (n + 1) ≫
        connecting R Lᶜ n := by
  exact connecting_naturality R (K ∪ L)ᶜ Lᶜ (ContinuousMap.id X)
    (unionComplement_subset_rightComplement K L) n

#print axioms restrictLeft_connecting
#print axioms restrictRight_connecting

end ConstructionTargets.CoefficientCompactSupportRestrictionNaturality
