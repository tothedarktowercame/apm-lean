import ConstructionTargets.CoefficientIntersectionRangeComparison

noncomputable section
namespace ConstructionTargets.CoefficientIntersectionRangeNaturality

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.CoefficientAmbientSubspaceRangeComparison
open ConstructionTargets.CoefficientAmbientSubspaceRangeNaturality
open ConstructionTargets.CoefficientIntersectionRangeComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]
abbrev chains := (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

private theorem intersection_inv_comp_left (A B : Set X) :
    (ambientIntersectionRangeIso A B).inv ≫
        ambientSubspaceRangeInclusion (Set.inter_subset_left) =
      subcomplexIntersectionToLeft (ambientSubspaceRange A) (ambientSubspaceRange B) := by
  rw [← ambientIntersectionRangeIso_hom_comp_left A B]
  simp

private theorem intersection_inv_comp_right (A B : Set X) :
    (ambientIntersectionRangeIso A B).inv ≫
        ambientSubspaceRangeInclusion (Set.inter_subset_right) =
      subcomplexIntersectionToRight (ambientSubspaceRange A) (ambientSubspaceRange B) := by
  rw [← ambientIntersectionRangeIso_hom_comp_right A B]
  simp

theorem chain_square_left (A B : Set X) :
    (intersectionChainsIso R A B).inv ≫ (rangeChainsIso R (A ∩ B)).hom ≫
        (chains R).map (TopCat.toSSet.map
          (topologicalSubspaceInclusion (Set.inter_subset_left))) =
      (chains R).map (subcomplexIntersectionToLeft
          (ambientSubspaceRange A) (ambientSubspaceRange B)) ≫
        (rangeChainsIso R A).hom := by
  rw [chain_square R Set.inter_subset_left]
  change (chains R).map (ambientIntersectionRangeIso A B).inv ≫
      ((chains R).map (ambientSubspaceRangeInclusion Set.inter_subset_left) ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, intersection_inv_comp_left]

theorem chain_square_right (A B : Set X) :
    (intersectionChainsIso R A B).inv ≫ (rangeChainsIso R (A ∩ B)).hom ≫
        (chains R).map (TopCat.toSSet.map
          (topologicalSubspaceInclusion (Set.inter_subset_right))) =
      (chains R).map (subcomplexIntersectionToRight
          (ambientSubspaceRange A) (ambientSubspaceRange B)) ≫
        (rangeChainsIso R B).hom := by
  rw [chain_square R Set.inter_subset_right]
  change (chains R).map (ambientIntersectionRangeIso A B).inv ≫
      ((chains R).map (ambientSubspaceRangeInclusion Set.inter_subset_right) ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, intersection_inv_comp_right]

theorem homology_square_left (A B : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap ((intersectionChainsIso R A B).inv ≫
      (rangeChainsIso R (A ∩ B)).hom) n ≫
      HomologicalComplex.homologyMap ((chains R).map (TopCat.toSSet.map
        (topologicalSubspaceInclusion (Set.inter_subset_left)))) n =
    HomologicalComplex.homologyMap ((chains R).map (subcomplexIntersectionToLeft
      (ambientSubspaceRange A) (ambientSubspaceRange B))) n ≫
      HomologicalComplex.homologyMap (rangeChainsIso R A).hom n := by
  simpa only [← HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f n) (chain_square_left R A B)

theorem homology_square_right (A B : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap ((intersectionChainsIso R A B).inv ≫
      (rangeChainsIso R (A ∩ B)).hom) n ≫
      HomologicalComplex.homologyMap ((chains R).map (TopCat.toSSet.map
        (topologicalSubspaceInclusion (Set.inter_subset_right)))) n =
    HomologicalComplex.homologyMap ((chains R).map (subcomplexIntersectionToRight
      (ambientSubspaceRange A) (ambientSubspaceRange B))) n ≫
      HomologicalComplex.homologyMap (rangeChainsIso R B).hom n := by
  simpa only [← HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f n) (chain_square_right R A B)

#print axioms chain_square_left
#print axioms chain_square_right
#print axioms homology_square_left
#print axioms homology_square_right
end ConstructionTargets.CoefficientIntersectionRangeNaturality
