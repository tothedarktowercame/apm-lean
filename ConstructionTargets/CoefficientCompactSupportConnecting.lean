import ConstructionTargets.CoefficientCompactSupportRestrictionNaturality

noncomputable section
namespace ConstructionTargets.CoefficientCompactSupportConnecting

open CategoryTheory Set
open ConstructionTargets.CoefficientPairSequence

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev relative (A : Set X) :=
  CoefficientRelativeSmall.relativeChains R A

/-- The actual relative connecting arrow for compact-support Mayer--Vietoris:
pair boundary for the intersection support, inclusion into `X`, then quotient
by the complement of the union support. -/
noncomputable def supportConnecting (K L : Set X) (n : ℕ) :
    (relative R (K ∩ L)ᶜ).homology (n + 1) ⟶
      (relative R (K ∪ L)ᶜ).homology n :=
  connecting R (K ∩ L)ᶜ n ≫
    HomologicalComplex.homologyMap
      (CoefficientRelativeSmall.subspaceMap R (K ∩ L)ᶜ) n ≫
    HomologicalComplex.homologyMap
      (projection R (K ∪ L)ᶜ) n

theorem supportConnecting_formula (K L : Set X) (n : ℕ) :
    supportConnecting R K L n =
      connecting R (K ∩ L)ᶜ n ≫
        HomologicalComplex.homologyMap
          (CoefficientRelativeSmall.subspaceMap R (K ∩ L)ᶜ) n ≫
        HomologicalComplex.homologyMap
          (projection R (K ∪ L)ᶜ) n := rfl

#print axioms supportConnecting
#print axioms supportConnecting_formula

end ConstructionTargets.CoefficientCompactSupportConnecting
