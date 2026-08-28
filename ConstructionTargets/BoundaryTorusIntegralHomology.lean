import ConstructionTargets.BoundaryTorusMayerVietorisAlgebra

/-!
# Integral homology integration for the boundary torus

This downstream file can import both the geometric Mayer--Vietoris coordinates
and the signed-fold algebra without creating an import cycle.
-/

open Set Topology CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.BoundaryTorusIntegralHomology

open ConstructionTargets.BoundaryTorusOpenCover
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusMayerVietorisAlgebra
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.TopologicalSumSingularHomology

private abbrev F (k : ℕ) :=
  (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

theorem left_threeFactor_eq_codiagonal (k : ℕ) :
    (overlapHomologyIsoCircleBiprod k).inv ≫
        (F k).map (TopCat.ofHom overlapToLeft) ≫
        (leftHomologyIsoCircle k).hom =
      biprod.desc (𝟙 (H k Circle)) (𝟙 (H k Circle)) := by
  simp only [overlapHomologyIsoCircleBiprod, Iso.trans_inv,
    leftHomologyIsoCircle,
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv_hom]
  unfold overlapHomologyIsoTwoCircles
  rw [singularHomologyIsoOfHomotopyEquiv_inv_local
    overlapHomotopyEquivTwoCircles k]
  have htail :
      ((F k).map (TopCat.ofHom twoCirclesToOverlap) ≫
          (F k).map (TopCat.ofHom overlapToLeft)) ≫
          (F k).map (TopCat.ofHom leftPieceRetraction) =
        (F k).map (TopCat.ofHom twoCircleFold) := by
    calc
      _ = (F k).map
          ((TopCat.ofHom twoCirclesToOverlap ≫
            TopCat.ofHom overlapToLeft) ≫
            TopCat.ofHom leftPieceRetraction) := by
        rw [Functor.map_comp, Functor.map_comp]
      _ = (F k).map (TopCat.ofHom leftOverlapComposite) := by rfl
      _ = _ := leftOverlapComposite_homologyMap k
  calc
    _ = (sumHomologyIsoBiprod Circle Circle k).inv ≫
        (((F k).map (TopCat.ofHom twoCirclesToOverlap) ≫
          (F k).map (TopCat.ofHom overlapToLeft)) ≫
          (F k).map (TopCat.ofHom leftPieceRetraction)) := by
      rfl
    _ = (sumHomologyIsoBiprod Circle Circle k).inv ≫
        (F k).map (TopCat.ofHom twoCircleFold) := by
      exact congrArg (fun q ↦
        (sumHomologyIsoBiprod Circle Circle k).inv ≫ q) htail
    _ = _ := sumCircleIso_inv_comp_foldHomologyMap k

theorem right_threeFactor_eq_codiagonal (k : ℕ) :
    (overlapHomologyIsoCircleBiprod k).inv ≫
        (F k).map (TopCat.ofHom overlapToRight) ≫
        (rightHomologyIsoCircle k).hom =
      biprod.desc (𝟙 (H k Circle)) (𝟙 (H k Circle)) := by
  simp only [overlapHomologyIsoCircleBiprod, Iso.trans_inv,
    rightHomologyIsoCircle,
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv_hom]
  unfold overlapHomologyIsoTwoCircles
  rw [singularHomologyIsoOfHomotopyEquiv_inv_local
    overlapHomotopyEquivTwoCircles k]
  have htail :
      ((F k).map (TopCat.ofHom twoCirclesToOverlap) ≫
          (F k).map (TopCat.ofHom overlapToRight)) ≫
          (F k).map (TopCat.ofHom rightPieceRetraction) =
        (F k).map (TopCat.ofHom twoCircleFold) := by
    calc
      _ = (F k).map
          ((TopCat.ofHom twoCirclesToOverlap ≫
            TopCat.ofHom overlapToRight) ≫
            TopCat.ofHom rightPieceRetraction) := by
        rw [Functor.map_comp, Functor.map_comp]
      _ = (F k).map (TopCat.ofHom rightOverlapComposite) := by rfl
      _ = _ := rightOverlapComposite_homologyMap k
  calc
    _ = (sumHomologyIsoBiprod Circle Circle k).inv ≫
        (((F k).map (TopCat.ofHom twoCirclesToOverlap) ≫
          (F k).map (TopCat.ofHom overlapToRight)) ≫
          (F k).map (TopCat.ofHom rightPieceRetraction)) := by
      rfl
    _ = (sumHomologyIsoBiprod Circle Circle k).inv ≫
        (F k).map (TopCat.ofHom twoCircleFold) := by
      exact congrArg (fun q ↦
        (sumHomologyIsoBiprod Circle Circle k).inv ≫ q) htail
    _ = _ := sumCircleIso_inv_comp_foldHomologyMap k

theorem mapIso_inv_codiagonal_comp {A B : AddCommGrpCat} (e : A ≅ B) :
    (biprod.mapIso e e).inv ≫
        biprod.desc (𝟙 A) (𝟙 A) ≫ e.hom =
      biprod.desc (𝟙 B) (𝟙 B) := by
  apply biprod.hom_ext'
  · simp
  · simp

theorem overlapInteger_left_component (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    ((overlapHomologyIsoCircleBiprod k ≪≫ biprod.mapIso e e).inv ≫
        (F k).map (TopCat.ofHom overlapToLeft)) ≫
        (leftHomologyIsoCircle k ≪≫ e).hom =
      intFold := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  calc
    _ = (biprod.mapIso e e).inv ≫
        (((overlapHomologyIsoCircleBiprod k).inv ≫
          (F k).map (TopCat.ofHom overlapToLeft)) ≫
          (leftHomologyIsoCircle k).hom) ≫ e.hom := by
      simp only [Category.assoc]
    _ = (biprod.mapIso e e).inv ≫
        biprod.desc (𝟙 (H k Circle)) (𝟙 (H k Circle)) ≫
          e.hom := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ (biprod.mapIso e e).inv ≫ q ≫ e.hom)
        (left_threeFactor_eq_codiagonal k)
    _ = _ := mapIso_inv_codiagonal_comp e

theorem overlapInteger_right_component (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    ((overlapHomologyIsoCircleBiprod k ≪≫ biprod.mapIso e e).inv ≫
        (F k).map (TopCat.ofHom overlapToRight)) ≫
        (rightHomologyIsoCircle k ≪≫ e).hom =
      intFold := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  calc
    _ = (biprod.mapIso e e).inv ≫
        (((overlapHomologyIsoCircleBiprod k).inv ≫
          (F k).map (TopCat.ofHom overlapToRight)) ≫
          (rightHomologyIsoCircle k).hom) ≫ e.hom := by
      simp only [Category.assoc]
    _ = (biprod.mapIso e e).inv ≫
        biprod.desc (𝟙 (H k Circle)) (𝟙 (H k Circle)) ≫
          e.hom := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ (biprod.mapIso e e).inv ≫ q ≫ e.hom)
        (right_threeFactor_eq_codiagonal k)
    _ = _ := mapIso_inv_codiagonal_comp e

noncomputable def overlapIntegerIso (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    H k Overlap ≅ BoundaryTorusMayerVietorisAlgebra.IntGroup ⊞
      BoundaryTorusMayerVietorisAlgebra.IntGroup :=
  overlapHomologyIsoCircleBiprod k ≪≫ biprod.mapIso e e

noncomputable def piecesIntegerIso (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    (H k leftOpen ⊞ H k rightOpen) ≅
      BoundaryTorusMayerVietorisAlgebra.IntGroup ⊞
        BoundaryTorusMayerVietorisAlgebra.IntGroup :=
  biprod.mapIso (leftHomologyIsoCircle k ≪≫ e)
    (rightHomologyIsoCircle k ≪≫ e)

#print axioms left_threeFactor_eq_codiagonal
#print axioms right_threeFactor_eq_codiagonal
#print axioms overlapInteger_left_component
#print axioms overlapInteger_right_component

end ConstructionTargets.BoundaryTorusIntegralHomology
