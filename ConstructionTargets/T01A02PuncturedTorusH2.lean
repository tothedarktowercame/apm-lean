import ConstructionTargets.T01A02PuncturedTorusDegreeTwoMVCover
import ConstructionTargets.T00A01MayerVietorisAdapters

open CategoryTheory CategoryTheory.Limits Set
open scoped ContinuousMap
noncomputable section

namespace ConstructionTargets.T01A02PuncturedTorus

open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.T00A01MayerVietorisAdapters
open ConstructionTargets.IntegralSingularHomologyComparison

/-- Integral second homology of the once-punctured torus vanishes. -/
theorem puncturedTorus_H2_isZero : IsZero (H 2 X) := by
  obtain ⟨C⟩ := puncturedTorusDegreeTwoMVCover
  have hleft : IsZero (SingularHomology 2 (TopCat.of C.leftPiece)) :=
    groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of C.leftPiece) 2
      C.left_H2_zero
  have hright : IsZero (SingularHomology 2 (TopCat.of C.rightPiece)) :=
    groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of C.rightPiece) 2
      C.right_H2_zero
  have hintersection : IsZero
      (SingularHomology 1 (TopCat.of (C.leftPiece ∩ C.rightPiece : Set X))) :=
    groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of (C.leftPiece ∩ C.rightPiece : Set X)) 1 C.intersection_H1_zero
  have hgroup : IsZero (SingularHomology 2 (TopCat.of X)) := by
    let hex := productionMayerVietoris_exact_union
      C.leftPiece C.rightPiece C.left_open C.right_open C.cover 1
    apply hex.isZero_X₂
    · exact ((biprod_isZero_iff _ _).mpr ⟨hleft, hright⟩).eq_of_src _ _
    · exact hintersection.eq_of_tgt _ _
  exact singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of X) 2 hgroup

abbrev H2 (Y : Type) [TopologicalSpace Y] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))

def H2map {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) : H2 Y ⟶ H2 Z :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

/-- A second-homology map factoring through a space with zero second
homology is zero. -/
theorem H2map_eq_zero_of_factor
    {Y Z W : Type} [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    (f : C(Y, Z)) (g : C(Y, W)) (i : C(W, Z))
    (hf : f = i.comp g) (hW : IsZero (H2 W)) :
    H2map f = 0 := by
  rw [hf]
  rw [show H2map (i.comp g) = H2map g ≫ H2map i by
    exact Functor.map_comp _ _ _]
  rw [hW.eq_of_tgt (H2map g) 0, zero_comp]

end ConstructionTargets.T01A02PuncturedTorus
