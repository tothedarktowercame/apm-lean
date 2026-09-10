import ConstructionTargets.CoefficientAmbientSubspaceRangeComparison

noncomputable section
namespace ConstructionTargets.CoefficientAmbientSubspaceRangeNaturality

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.CoefficientAmbientSubspaceRangeComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains := (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

theorem chain_square {A B : Set X} (h : A ⊆ B) :
    (rangeChainsIso R A).hom ≫
        (chains R).map (TopCat.toSSet.map (topologicalSubspaceInclusion h)) =
      (chains R).map (ambientSubspaceRangeInclusion h) ≫
        (rangeChainsIso R B).hom := by
  change (chains R).map _ ≫ (chains R).map _ =
    (chains R).map _ ≫ (chains R).map _
  simpa only [← Functor.map_comp] using
    congrArg (chains R).map (ambientSubspaceRangeInclusion_square h)

theorem homology_square {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    (rangeHomologyIso R A n).hom ≫
        HomologicalComplex.homologyMap
          ((chains R).map (TopCat.toSSet.map (topologicalSubspaceInclusion h))) n =
      HomologicalComplex.homologyMap
          ((chains R).map (ambientSubspaceRangeInclusion h)) n ≫
        (rangeHomologyIso R B n).hom := by
  change HomologicalComplex.homologyMap (rangeChainsIso R A).hom n ≫ _ =
    _ ≫ HomologicalComplex.homologyMap (rangeChainsIso R B).hom n
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, chain_square]

#print axioms chain_square
#print axioms homology_square
end ConstructionTargets.CoefficientAmbientSubspaceRangeNaturality
