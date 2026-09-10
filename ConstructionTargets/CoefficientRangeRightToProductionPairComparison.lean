import ConstructionTargets.CoefficientRangeRightRelativeCokernelComparison
import ConstructionTargets.CoefficientNestedSubspaceIntersectionComparison

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ConstructionTargets.CoefficientRangeRightToProductionPairComparison

open ConstructionTargets.SingularExcision
open ConstructionTargets.NestedSubspaceIntersectionComparison
open ConstructionTargets.CoefficientRangeRightRelativeCokernelComparison
open ConstructionTargets.CoefficientNestedSubspaceIntersectionComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] (U V : Set X)

private abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)
private abbrev leftRange := ambientSubspaceRange U
private abbrev rightRange := ambientSubspaceRange V

noncomputable def rangeRightRelativeToProductionPairIso :
    cokernel ((chains R).map (subcomplexIntersectionToRight
      (leftRange U) (rightRange V))) ≅
      CoefficientRelativeSmall.relativeChains R (nestedIntersection U V) :=
  rangeRightRelativeCokernelIso R U V ≪≫
    intersectionNestedRelativeChainsIso R U V

#print axioms rangeRightRelativeToProductionPairIso
end ConstructionTargets.CoefficientRangeRightToProductionPairComparison
