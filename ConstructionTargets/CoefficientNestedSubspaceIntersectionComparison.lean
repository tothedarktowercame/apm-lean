import ConstructionTargets.CoefficientPairConnectingMayerVietorisComparison
import ConstructionTargets.NestedSubspaceIntersectionComparison

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ConstructionTargets.CoefficientNestedSubspaceIntersectionComparison

open ConstructionTargets.NestedSubspaceIntersectionComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] (U V : Set X)

private abbrev chainsFunctor :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)

noncomputable def intersectionNestedChainsIso :
    CoefficientH0.SingularChains R (TopCat.of (U ∩ V : Set X)) ≅
      CoefficientH0.SingularChains R (TopCat.of (nestedIntersection U V)) :=
  (chainsFunctor R).mapIso
    (TopCat.isoOfHomeo (intersectionNestedHomeomorph U V))

theorem intersectionNested_chain_square :
    (intersectionNestedChainsIso R U V).hom ≫
        (chainsFunctor R).map
          (TopCat.ofHom (nestedIntersectionInclusionContinuous U V)) =
      (chainsFunctor R).map
        (TopCat.ofHom (intersectionToRightContinuous U V)) := by
  dsimp [intersectionNestedChainsIso]
  rw [← Functor.map_comp]
  congr 1

noncomputable def intersectionNestedHomologyIso (n : ℕ) :
    (CoefficientH0.SingularChains R (TopCat.of (U ∩ V : Set X))).homology n ≅
      (CoefficientH0.SingularChains R
        (TopCat.of (nestedIntersection U V))).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (intersectionNestedChainsIso R U V)

theorem intersectionNested_homology_square (n : ℕ) :
    (intersectionNestedHomologyIso R U V n).hom ≫
        HomologicalComplex.homologyMap
          ((chainsFunctor R).map
            (TopCat.ofHom (nestedIntersectionInclusionContinuous U V))) n =
      HomologicalComplex.homologyMap
        ((chainsFunctor R).map
          (TopCat.ofHom (intersectionToRightContinuous U V))) n := by
  change HomologicalComplex.homologyMap _ n ≫
      HomologicalComplex.homologyMap _ n = HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp,
    intersectionNested_chain_square]

noncomputable def intersectionNestedRelativeChainsIso :
    cokernel ((chainsFunctor R).map
      (TopCat.ofHom (intersectionToRightContinuous U V))) ≅
      CoefficientRelativeSmall.relativeChains R (nestedIntersection U V) :=
  cokernel.mapIso
    ((chainsFunctor R).map
      (TopCat.ofHom (intersectionToRightContinuous U V)))
    (CoefficientRelativeSmall.subspaceMap R (nestedIntersection U V))
    (intersectionNestedChainsIso R U V) (Iso.refl _)
    (by
      dsimp only [CoefficientRelativeSmall.subspaceMap,
        SingularHomologyConcrete.subspaceInclusion,
        nestedIntersectionInclusionContinuous]
      simpa using (intersectionNested_chain_square R U V).symm)

#print axioms intersectionNested_chain_square
#print axioms intersectionNested_homology_square
#print axioms intersectionNestedRelativeChainsIso

end ConstructionTargets.CoefficientNestedSubspaceIntersectionComparison
