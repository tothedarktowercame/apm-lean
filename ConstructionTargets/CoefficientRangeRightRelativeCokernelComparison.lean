import ConstructionTargets.CoefficientRangeIntersectionToRightComparison

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ConstructionTargets.CoefficientRangeRightRelativeCokernelComparison

open ConstructionTargets.SingularExcision
open ConstructionTargets.NestedSubspaceIntersectionComparison
open ConstructionTargets.CoefficientRangeIntersectionToRightComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] (U V : Set X)

private abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)
private abbrev leftRange := ambientSubspaceRange U
private abbrev rightRange := ambientSubspaceRange V

noncomputable def rangeRightRelativeCokernelIso :
    cokernel ((chains R).map (subcomplexIntersectionToRight
      (leftRange U) (rightRange V))) ≅
      cokernel ((chains R).map (TopCat.toSSet.map
        (TopCat.ofHom (intersectionToRightContinuous U V)))) :=
  cokernel.mapIso
    ((chains R).map (subcomplexIntersectionToRight
      (leftRange U) (rightRange V)))
    ((chains R).map (TopCat.toSSet.map
      (TopCat.ofHom (intersectionToRightContinuous U V))))
    (rangeIntersectionChainsIso R U V)
    (CoefficientAmbientSubspaceRangeComparison.rangeChainsIso R V)
    (rangeIntersectionToRight_chain_square R U V).symm

#print axioms rangeRightRelativeCokernelIso
end ConstructionTargets.CoefficientRangeRightRelativeCokernelComparison
