import ConstructionTargets.CoefficientNestedSubspaceIntersectionComparison
import ConstructionTargets.CoefficientIntersectionRangeNaturality

/-!
# From the range-subcomplex relative cokernel to a production pair

This file transports the right-hand relative cokernel of the range-subcomplex
Mayer--Vietoris square to relative singular chains of the corresponding nested
topological pair.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.CoefficientRangeIntersectionToRightComparison

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientPairConnectingMayerVietorisComparison
open ConstructionTargets.NestedSubspaceIntersectionComparison
open ConstructionTargets.CoefficientNestedSubspaceIntersectionComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] (U V : Set X)

private abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)

private abbrev leftRange := ambientSubspaceRange U
private abbrev rightRange := ambientSubspaceRange V

/-- Chains on the intersection of the two ambient ranges are canonically
chains on the ordinary topological intersection. -/
noncomputable def rangeIntersectionChainsIso :
    (chains R).obj ((leftRange U ⊓ rightRange V :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) ≅
      CoefficientH0.SingularChains R (TopCat.of (U ∩ V : Set X)) :=
  (CoefficientIntersectionRangeComparison.intersectionChainsIso R U V).symm ≪≫
    CoefficientAmbientSubspaceRangeComparison.rangeChainsIso R (U ∩ V)

/-- The range-intersection inclusion into the right range becomes the literal
topological inclusion `(U ∩ V) → V`. -/
theorem rangeIntersectionToRight_chain_square :
    (rangeIntersectionChainsIso R U V).hom ≫
        (chains R).map
          (TopCat.toSSet.map (TopCat.ofHom (intersectionToRightContinuous U V))) =
      (chains R).map (subcomplexIntersectionToRight
          (leftRange U) (rightRange V)) ≫
        (CoefficientAmbientSubspaceRangeComparison.rangeChainsIso R V).hom := by
  simpa [rangeIntersectionChainsIso, intersectionToRightContinuous,
    topologicalSubspaceInclusion] using
    (CoefficientIntersectionRangeNaturality.chain_square_right R U V)

#print axioms rangeIntersectionChainsIso
#print axioms rangeIntersectionToRight_chain_square

end ConstructionTargets.CoefficientRangeIntersectionToRightComparison
