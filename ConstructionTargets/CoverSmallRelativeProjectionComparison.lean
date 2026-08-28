import ConstructionTargets.UnionToRelativeProductionComparison

/-!
# Cover-small inclusion and the relative projection

For an ambient cover `U ∪ V = univ`, this file compares the map obtained from
the range-subcomplex pushout with the actual absolute-to-relative projection
for `(X,U)`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.CoverSmallRelativeProjectionComparison

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.NestedSubspaceIntersectionComparison
open ConstructionTargets.UnionToRelativeProductionComparison

variable {X : Type} [TopologicalSpace X] (U V : Set X)

private abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

private abbrev leftRange := ambientSubspaceRange U
private abbrev rightRange := ambientSubspaceRange V

/-- The range-chain presentation followed by the actual subspace inclusion is
the inclusion of the range subcomplex into ambient singular chains. -/
theorem ambientRangeChainsIso_hom_comp_singularSubspaceMap (A : Set X) :
    (ambientSubspaceRangeChainsIso A).hom ≫ singularSubspaceMap A =
      chains.map (ambientSubspaceRange A).ι := by
  change chains.map _ ≫ chains.map _ = chains.map _
  rw [← Functor.map_comp]
  congr 1
  exact rangeIso_hom_comp _

/-- Inclusion of the right cover member into the ambient space. -/
def rightToAmbient : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩

theorem rightToAmbient_maps_nested_to_left :
    Set.MapsTo (rightToAmbient V) (nestedIntersection U V) U := by
  intro x hx
  exact hx

/-- The production relative-chain map `(V,U ∩ V) → (X,U)`. -/
noncomputable def rightPairToAmbientRelative :
    RelativeSingularChains (nestedIntersection U V) ⟶
      RelativeSingularChains U :=
  relativeSingularMap (nestedIntersection U V) U (rightToAmbient V)
    (rightToAmbient_maps_nested_to_left U V)

/-- Cover-small chains included into ambient chains and then projected to the
relative chain complex of `(X,U)`. -/
noncomputable def coverSmallToAmbientRelative :
    chains.obj ((leftRange U ⊔ rightRange V :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) ⟶
      RelativeSingularChains U :=
  chains.map ((leftRange U ⊔ rightRange V).ι) ≫
    relativeSingularProjection U

/-- On the left member, cover-small inclusion followed by relative projection
vanishes. -/
theorem leftRange_comp_coverSmallToAmbientRelative :
    chains.map (subcomplexLeftToUnion (leftRange U) (rightRange V)) ≫
        coverSmallToAmbientRelative U V = 0 := by
  rw [coverSmallToAmbientRelative]
  rw [← Category.assoc]
  slice_lhs 1 2 => rw [← Functor.map_comp]
  have hinc : subcomplexLeftToUnion (leftRange U) (rightRange V) ≫
      (leftRange U ⊔ rightRange V).ι = (leftRange U).ι := rfl
  rw [hinc]
  rw [← ambientRangeChainsIso_hom_comp_singularSubspaceMap U]
  calc
    ((ambientSubspaceRangeChainsIso U).hom ≫
        (singularPairShortComplex U).f) ≫ (singularPairShortComplex U).g =
      (ambientSubspaceRangeChainsIso U).hom ≫
        ((singularPairShortComplex U).f ≫
          (singularPairShortComplex U).g) := Category.assoc _ _ _
    _ = (ambientSubspaceRangeChainsIso U).hom ≫ 0 :=
      congrArg (fun k ↦ (ambientSubspaceRangeChainsIso U).hom ≫ k)
        (singularPairShortComplex U).zero
    _ = 0 := comp_zero

/-- On the right member, the pushout map followed by the map of pairs agrees
with ambient inclusion followed by relative projection. -/
theorem rightRange_comp_pushoutThenAmbientPair :
    chains.map (subcomplexRightToUnion (leftRange U) (rightRange V)) ≫
        coverSmallUnionToProductionRelative U V ≫
          rightPairToAmbientRelative U V =
      chains.map (rightRange V).ι ≫ relativeSingularProjection U := by
  rw [← Category.assoc,
    rightRange_comp_coverSmallUnionToProductionRelative]
  dsimp only [rightPairToAmbientRelative]
  rw [Category.assoc]
  rw [← relativeSingularMap_projection_naturality
    (nestedIntersection U V) U (rightToAmbient V)
      (rightToAmbient_maps_nested_to_left U V)]
  change ((ambientSubspaceRangeChainsIso V).hom ≫ singularSubspaceMap V) ≫
      relativeSingularProjection U = _
  rw [ambientRangeChainsIso_hom_comp_singularSubspaceMap V]
  rfl

/-- The cover-small pushout construction is exactly ambient inclusion followed
by the production relative projection, after mapping the right pair into the
ambient pair. -/
theorem coverSmall_pushout_relative_eq_projection
    : coverSmallUnionToProductionRelative U V ≫
        rightPairToAmbientRelative U V =
      coverSmallToAmbientRelative U V := by
  apply (subcomplexChains_isPushout (leftRange U) (rightRange V)).hom_ext
  · calc
      _ = (chains.map (subcomplexLeftToUnion (leftRange U) (rightRange V)) ≫
            coverSmallUnionToProductionRelative U V) ≫
            rightPairToAmbientRelative U V := (Category.assoc _ _ _).symm
      _ = 0 := by
        rw [leftRange_comp_coverSmallUnionToProductionRelative, zero_comp]
      _ = _ := (leftRange_comp_coverSmallToAmbientRelative U V).symm
  · rw [rightRange_comp_pushoutThenAmbientPair]
    rw [coverSmallToAmbientRelative]
    rw [← Category.assoc, ← Functor.map_comp]
    rfl

/-- Homology-level form of the cover-small projection comparison. -/
theorem coverSmall_pushout_relative_homology_eq_projection
    (n : ℕ) :
    HomologicalComplex.homologyMap
          (coverSmallUnionToProductionRelative U V) n ≫
        HomologicalComplex.homologyMap
          (rightPairToAmbientRelative U V) n =
      HomologicalComplex.homologyMap
        (coverSmallToAmbientRelative U V) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    coverSmall_pushout_relative_eq_projection U V]

#print axioms ambientRangeChainsIso_hom_comp_singularSubspaceMap
#print axioms coverSmall_pushout_relative_eq_projection
#print axioms coverSmall_pushout_relative_homology_eq_projection

end ConstructionTargets.CoverSmallRelativeProjectionComparison
