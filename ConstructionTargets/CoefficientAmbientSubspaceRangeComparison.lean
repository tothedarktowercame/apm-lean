import ConstructionTargets.CoefficientCompactComplementCoverSequence

noncomputable section
namespace ConstructionTargets.CoefficientAmbientSubspaceRangeComparison

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularHomologyConcrete

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains := (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

noncomputable def rangeChainsIso (A : Set X) :
    (chains R).obj (ambientSubspaceRange A : SSet) ≅
      (chains R).obj (TopCat.toSSet.obj (TopCat.of A)) :=
  (chains R).mapIso
    (asIso (Subfunctor.toRange (TopCat.toSSet.map (subspaceInclusion A)))).symm

noncomputable def rangeHomologyIso (A : Set X) (n : ℕ) :
    ((chains R).obj (ambientSubspaceRange A : SSet)).homology n ≅
      ((chains R).obj (TopCat.toSSet.obj (TopCat.of A))).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (rangeChainsIso R A)

theorem rangeHomologyIso_hom (A : Set X) (n : ℕ) :
    (rangeHomologyIso R A n).hom =
      HomologicalComplex.homologyMap (rangeChainsIso R A).hom n := rfl

theorem rangeHomologyIso_inv (A : Set X) (n : ℕ) :
    (rangeHomologyIso R A n).inv =
      HomologicalComplex.homologyMap (rangeChainsIso R A).inv n := rfl

#print axioms rangeChainsIso
#print axioms rangeHomologyIso
#print axioms rangeHomologyIso_hom
#print axioms rangeHomologyIso_inv
end ConstructionTargets.CoefficientAmbientSubspaceRangeComparison
