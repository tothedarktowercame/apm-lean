import ConstructionTargets.NestedSubspaceIntersectionComparison

/-!
# From the range-subcomplex relative cokernel to a production pair

This file transports the right-hand relative cokernel of the range-subcomplex
Mayer--Vietoris square to relative singular chains of the corresponding nested
topological pair.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.UnionToRelativeProductionComparison

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.PairConnectingMayerVietorisComparison
open ConstructionTargets.NestedSubspaceIntersectionComparison

variable {X : Type} [TopologicalSpace X] (U V : Set X)

private abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

private abbrev leftRange := ambientSubspaceRange U
private abbrev rightRange := ambientSubspaceRange V

/-- Chains on the intersection of the two ambient ranges are canonically
chains on the ordinary topological intersection. -/
noncomputable def rangeIntersectionChainsIso :
    chains.obj ((leftRange U ⊓ rightRange V :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) ≅
      SingularChains (TopCat.of (U ∩ V : Set X)) :=
  (ambientIntersectionRangeChainsIso U V).symm ≪≫
    ambientSubspaceRangeChainsIso (U ∩ V)

/-- The range-intersection inclusion into the right range becomes the literal
topological inclusion `(U ∩ V) → V`. -/
theorem rangeIntersectionToRight_chain_square :
    (rangeIntersectionChainsIso U V).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map
            (TopCat.ofHom (intersectionToRightContinuous U V)) =
      chains.map (subcomplexIntersectionToRight
          (leftRange U) (rightRange V)) ≫
        (ambientSubspaceRangeChainsIso V).hom := by
  apply (cancel_epi (ambientIntersectionRangeChainsIso U V).hom).1
  simp only [rangeIntersectionChainsIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  slice_lhs 1 2 => rw [Iso.hom_inv_id]
  rw [Category.id_comp]
  slice_rhs 1 2 => rw [ambientIntersectionRangeChainsIso_hom_comp_right]
  rw [← ambientSubspaceRangeChainsIso_naturality
    (show U ∩ V ⊆ V from Set.inter_subset_right)]
  congr 2

/-- The right relative cokernel in the range-subcomplex pushout is the direct
relative cokernel for the literal inclusion `(U ∩ V) → V`. -/
noncomputable def rangeRightRelativeCokernelIso :
    cokernel (chains.map (subcomplexIntersectionToRight
      (leftRange U) (rightRange V))) ≅
      cokernel (((AlgebraicTopology.singularChainComplexFunctor
        AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom (intersectionToRightContinuous U V))) :=
  cokernel.mapIso
    (chains.map (subcomplexIntersectionToRight
      (leftRange U) (rightRange V)))
    (((AlgebraicTopology.singularChainComplexFunctor
      AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (intersectionToRightContinuous U V)))
    (rangeIntersectionChainsIso U V)
    (ambientSubspaceRangeChainsIso V)
    (rangeIntersectionToRight_chain_square U V).symm

/-- Complete transport of the range-subcomplex relative cokernel to production
relative singular chains of the nested pair inside `V`. -/
noncomputable def rangeRightRelativeToProductionPairIso :
    cokernel (chains.map (subcomplexIntersectionToRight
      (leftRange U) (rightRange V))) ≅
      RelativeSingularChains (nestedIntersection U V) :=
  rangeRightRelativeCokernelIso U V ≪≫
    intersectionNestedRelativeChainsIso U V

/-- The pushout-derived map from cover-small union chains, now valued in the
production relative singular chains of the nested pair. -/
noncomputable def coverSmallUnionToProductionRelative :
    chains.obj ((leftRange U ⊔ rightRange V :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) ⟶
      RelativeSingularChains (nestedIntersection U V) :=
  unionToRightRelative (leftRange U) (rightRange V) ≫
    (rangeRightRelativeToProductionPairIso U V).hom

/-- The transported union-to-relative map still kills the left cover member. -/
theorem leftRange_comp_coverSmallUnionToProductionRelative :
    chains.map (subcomplexLeftToUnion (leftRange U) (rightRange V)) ≫
      coverSmallUnionToProductionRelative U V = 0 := by
  dsimp only [coverSmallUnionToProductionRelative]
  have h := congrArg
    (fun k ↦ k ≫ (rangeRightRelativeToProductionPairIso U V).hom)
    (leftToUnion_unionToRightRelative (leftRange U) (rightRange V))
  simpa only [Category.assoc, zero_comp] using h

/-- On the right cover member, the transported pushout map is the ordinary
absolute-to-relative projection of the nested topological pair. -/
theorem rightRange_comp_coverSmallUnionToProductionRelative :
    chains.map (subcomplexRightToUnion (leftRange U) (rightRange V)) ≫
        coverSmallUnionToProductionRelative U V =
      (ambientSubspaceRangeChainsIso V).hom ≫
        relativeSingularProjection (nestedIntersection U V) := by
  calc
    _ = cokernel.π (chains.map (subcomplexIntersectionToRight
          (leftRange U) (rightRange V))) ≫
        (rangeRightRelativeToProductionPairIso U V).hom := by
      simpa only [coverSmallUnionToProductionRelative, Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (rangeRightRelativeToProductionPairIso U V).hom)
          (rightToUnion_unionToRightRelative (leftRange U) (rightRange V))
    _ = _ := by
      dsimp [rangeRightRelativeToProductionPairIso,
        rangeRightRelativeCokernelIso,
        intersectionNestedRelativeChainsIso,
        intersectionNestedCokernelIso]
      simp
      apply (cancel_mono
        (relativeSingularChainsIsoCokernelSubspaceMap
          (nestedIntersection U V)).hom).1
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        relativeProjection_comp_cokernelIso_hom]

#print axioms rangeIntersectionToRight_chain_square
#print axioms rangeRightRelativeToProductionPairIso
#print axioms leftRange_comp_coverSmallUnionToProductionRelative
#print axioms rightRange_comp_coverSmallUnionToProductionRelative

end ConstructionTargets.UnionToRelativeProductionComparison
