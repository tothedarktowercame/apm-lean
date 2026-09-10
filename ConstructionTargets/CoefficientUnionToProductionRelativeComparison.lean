import ConstructionTargets.CoefficientRangeRightToProductionPairComparison

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ConstructionTargets.CoefficientUnionToProductionRelativeComparison

open ConstructionTargets.SingularExcision
open ConstructionTargets.NestedSubspaceIntersectionComparison
open ConstructionTargets.CoefficientPairConnectingMayerVietorisComparison
open ConstructionTargets.CoefficientRangeRightToProductionPairComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] (U V : Set X)

private abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)
private abbrev leftRange := ambientSubspaceRange U
private abbrev rightRange := ambientSubspaceRange V

noncomputable def unionToProductionRelative :
    (chains R).obj ((leftRange U ⊔ rightRange V :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) ⟶
      CoefficientRelativeSmall.relativeChains R (nestedIntersection U V) :=
  unionToRightRelative R (leftRange U) (rightRange V) ≫
    (rangeRightRelativeToProductionPairIso R U V).hom

theorem leftToUnion_unionToProductionRelative :
    (chains R).map (subcomplexLeftToUnion (leftRange U) (rightRange V)) ≫
        unionToProductionRelative R U V = 0 := by
  rw [unionToProductionRelative, ← Category.assoc,
    leftToUnion_unionToRightRelative, zero_comp]

theorem rightToUnion_unionToProductionRelative :
    (chains R).map (subcomplexRightToUnion (leftRange U) (rightRange V)) ≫
        unionToProductionRelative R U V =
      (CoefficientAmbientSubspaceRangeComparison.rangeChainsIso R V).hom ≫
        cokernel.π (CoefficientRelativeSmall.subspaceMap R
          (nestedIntersection U V)) := by
  rw [unionToProductionRelative, ← Category.assoc,
    rightToUnion_unionToRightRelative]
  simp [rangeRightRelativeToProductionPairIso,
    CoefficientRangeRightRelativeCokernelComparison.rangeRightRelativeCokernelIso,
    CoefficientNestedSubspaceIntersectionComparison.intersectionNestedRelativeChainsIso,
    cokernel.mapIso]
  dsimp only [cokernel.map]
  apply (cancel_epi
    (CoefficientAmbientSubspaceRangeComparison.rangeChainsIso R V).hom).2
  change cokernel.π
      ((chains R).map (TopCat.toSSet.map
        (TopCat.ofHom (intersectionToRightContinuous U V)))) ≫
      cokernel.desc _
        (cokernel.π (CoefficientRelativeSmall.subspaceMap R
          (nestedIntersection U V))) _ =
    cokernel.π (CoefficientRelativeSmall.subspaceMap R
      (nestedIntersection U V))
  exact cokernel.π_desc _ _ _

#print axioms unionToProductionRelative
#print axioms leftToUnion_unionToProductionRelative
#print axioms rightToUnion_unionToProductionRelative
end ConstructionTargets.CoefficientUnionToProductionRelativeComparison
