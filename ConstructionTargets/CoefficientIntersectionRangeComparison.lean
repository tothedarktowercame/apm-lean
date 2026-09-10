import ConstructionTargets.CoefficientAmbientSubspaceRangeNaturality

noncomputable section
namespace ConstructionTargets.CoefficientIntersectionRangeComparison

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientAmbientSubspaceRangeComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains := (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

noncomputable def intersectionChainsIso (A B : Set X) :
    (chains R).obj (ambientSubspaceRange (A ∩ B) : SSet) ≅
      (chains R).obj ((ambientSubspaceRange A ⊓ ambientSubspaceRange B :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) :=
  (chains R).mapIso (ambientIntersectionRangeIso A B)

noncomputable def intersectionHomologyIso (A B : Set X) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (intersectionChainsIso R A B)

/-- Forward comparison from the actual MV intersection-range term to
coefficient homology of the literal topological intersection subtype. -/
noncomputable def infimumToIntersectionHomologyIso (A B : Set X) (n : ℕ) :=
  (intersectionHomologyIso R A B n).symm ≪≫ rangeHomologyIso R (A ∩ B) n

theorem infimumToIntersectionHomologyIso_hom (A B : Set X) (n : ℕ) :
    (infimumToIntersectionHomologyIso R A B n).hom =
      (intersectionHomologyIso R A B n).inv ≫
        (rangeHomologyIso R (A ∩ B) n).hom := rfl

#print axioms intersectionChainsIso
#print axioms intersectionHomologyIso
#print axioms infimumToIntersectionHomologyIso
#print axioms infimumToIntersectionHomologyIso_hom
end ConstructionTargets.CoefficientIntersectionRangeComparison
