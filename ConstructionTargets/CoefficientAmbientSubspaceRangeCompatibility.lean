import ConstructionTargets.CoefficientSubspaceUnionRestrictedRangeIso
import ConstructionTargets.CoefficientRelativeSmall

noncomputable section
namespace ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility

open CategoryTheory
open ConstructionTargets.SingularExcision

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)

noncomputable def ambientSubspaceRangeChainsIso (A : Set X) :
    (chains R).obj (ambientSubspaceRange A : SSet) ≅
      CoefficientH0.SingularChains R (TopCat.of A) :=
  (chains R).mapIso
    (asIso (Subfunctor.toRange (TopCat.toSSet.map
      (SingularHomologyConcrete.subspaceInclusion A)))).symm

/-- The coefficient-chain range presentation followed by the actual subspace
inclusion is the inclusion of the range subcomplex into ambient chains. -/
theorem ambientSubspaceRangeChainsIso_hom_comp_subspaceMap (A : Set X) :
    (ambientSubspaceRangeChainsIso R A).hom ≫
        CoefficientRelativeSmall.subspaceMap R A =
      (chains R).map (ambientSubspaceRange A).ι := by
  change (chains R).map _ ≫ (chains R).map _ = (chains R).map _
  rw [← Functor.map_comp]
  congr 1
  exact rangeIso_hom_comp _

#print axioms ambientSubspaceRangeChainsIso_hom_comp_subspaceMap
end ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
