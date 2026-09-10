import ConstructionTargets.CoefficientCompactComplementHomologyTransport
set_option maxHeartbeats 800000

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementHomologySquares

open CategoryTheory Set
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementSmallComparison
open ConstructionTargets.CoefficientCompactComplementPairHomeomorph
open ConstructionTargets.CoefficientCompactComplementHomologyTransport

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

theorem left_chain_square (K L : Set X) :
    (leftChainsIso R K L).hom ≫
        (chains R).map (TopCat.ofHom (originalLeftInclusion K)) =
      (chains R).map (TopCat.ofHom (nestedLeftInclusion K L)) := by
  rw [show (leftChainsIso R K L).hom =
      (chains R).map (TopCat.isoOfHomeo (leftHomeomorph K L)).hom from rfl]
  rw [← Functor.map_comp]
  apply congrArg (chains R).map
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem right_chain_square (K L : Set X) :
    (rightChainsIso R K L).hom ≫
        (chains R).map (TopCat.ofHom (originalRightInclusion L)) =
      (chains R).map (TopCat.ofHom (nestedRightInclusion K L)) := by
  rw [show (rightChainsIso R K L).hom =
      (chains R).map (TopCat.isoOfHomeo (rightHomeomorph K L)).hom from rfl]
  rw [← Functor.map_comp]
  apply congrArg (chains R).map
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem overlap_chain_square (K L : Set X) :
    (overlapChainsIso R K L).hom ≫
        (chains R).map (TopCat.ofHom (originalOverlapInclusion K L)) =
      (chains R).map (TopCat.ofHom (nestedOverlapInclusion K L)) := by
  rw [show (overlapChainsIso R K L).hom =
      (chains R).map (TopCat.isoOfHomeo (overlapHomeomorph K L)).hom from rfl]
  rw [← Functor.map_comp]
  apply congrArg (chains R).map
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem left_homology_square (K L : Set X) (n : ℕ) :
    (leftHomologyIso R K L n).hom ≫
        HomologicalComplex.homologyMap
          ((chains R).map (TopCat.ofHom (originalLeftInclusion K))) n =
      HomologicalComplex.homologyMap
        ((chains R).map (TopCat.ofHom (nestedLeftInclusion K L))) n := by
  change HomologicalComplex.homologyMap (leftChainsIso R K L).hom n ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp, left_chain_square]

theorem right_homology_square (K L : Set X) (n : ℕ) :
    (rightHomologyIso R K L n).hom ≫
        HomologicalComplex.homologyMap
          ((chains R).map (TopCat.ofHom (originalRightInclusion L))) n =
      HomologicalComplex.homologyMap
        ((chains R).map (TopCat.ofHom (nestedRightInclusion K L))) n := by
  change HomologicalComplex.homologyMap (rightChainsIso R K L).hom n ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp, right_chain_square]

theorem overlap_homology_square (K L : Set X) (n : ℕ) :
    (overlapHomologyIso R K L n).hom ≫
        HomologicalComplex.homologyMap
          ((chains R).map (TopCat.ofHom (originalOverlapInclusion K L))) n =
      HomologicalComplex.homologyMap
        ((chains R).map (TopCat.ofHom (nestedOverlapInclusion K L))) n := by
  change HomologicalComplex.homologyMap (overlapChainsIso R K L).hom n ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp, overlap_chain_square]

#print axioms left_chain_square
#print axioms right_chain_square
#print axioms overlap_chain_square
#print axioms left_homology_square
#print axioms right_homology_square
#print axioms overlap_homology_square

end ConstructionTargets.CoefficientCompactComplementHomologySquares
