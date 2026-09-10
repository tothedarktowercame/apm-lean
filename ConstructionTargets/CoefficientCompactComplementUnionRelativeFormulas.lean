import ConstructionTargets.CoefficientCompactComplementUnionToRelative
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementUnionRelativeFormulas
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientUnionToProductionRelativeComparison
open ConstructionTargets.CoefficientCompactComplementUnionToRelative
open ConstructionTargets.NestedSubspaceIntersectionComparison
variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]
private abbrev chains := (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
theorem compactUnionToRelative_left (K L : Set X) :
    (chains R).map (subcomplexLeftToUnion
      (ambientSubspaceRange (left K L)) (ambientSubspaceRange (right K L))) ≫
      compactUnionToRelative R K L = 0 :=
  leftToUnion_unionToProductionRelative R (left K L) (right K L)
theorem compactUnionToRelative_right (K L : Set X) :
    (chains R).map (subcomplexRightToUnion
      (ambientSubspaceRange (left K L)) (ambientSubspaceRange (right K L))) ≫
      compactUnionToRelative R K L =
    (CoefficientAmbientSubspaceRangeComparison.rangeChainsIso R (right K L)).hom ≫
      cokernel.π (CoefficientRelativeSmall.subspaceMap R
        (nestedIntersection (left K L) (right K L))) :=
  rightToUnion_unionToProductionRelative R (left K L) (right K L)
#print axioms compactUnionToRelative_left
#print axioms compactUnionToRelative_right
end ConstructionTargets.CoefficientCompactComplementUnionRelativeFormulas
