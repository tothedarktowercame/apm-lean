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

theorem productionIntersection_left_map_eq (k : ℕ) :
    productionIntersectionArrow leftOpen rightOpen k ≫ biprod.fst =
      (F k).map (TopCat.ofHom overlapToLeft) := by
  simp only [productionIntersectionArrow, biprod.lift_fst]
  rfl

theorem productionIntersection_right_map_eq (k : ℕ) :
    productionIntersectionArrow leftOpen rightOpen k ≫ biprod.snd =
      -(F k).map (TopCat.ofHom overlapToRight) := by
  simp only [productionIntersectionArrow, biprod.lift_snd]
  rfl

/-- In integral circle coordinates, the actual production intersection map is
the signed fold.  The statement is uniform in the degree and in the chosen
integer coordinate on circle homology; the applications below use it in
degrees zero and one. -/
theorem productionIntersectionArrow_integer_conjugacy (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    (overlapIntegerIso k e).inv ≫
        productionIntersectionArrow leftOpen rightOpen k ≫
        (piecesIntegerIso k e).hom =
      intSignedFold := by
  apply biprod.hom_ext
  · rw [intSignedFold_fst]
    calc
      _ = (overlapIntegerIso k e).inv ≫
          (productionIntersectionArrow leftOpen rightOpen k ≫ biprod.fst) ≫
          (leftHomologyIsoCircle k ≪≫ e).hom := by
        rw [piecesIntegerIso, biprod.mapIso_hom]
        simpa only [Category.assoc] using congrArg
          (fun q ↦ ((overlapIntegerIso k e).inv ≫
            productionIntersectionArrow leftOpen rightOpen k) ≫ q)
          (biprod.map_fst (leftHomologyIsoCircle k ≪≫ e).hom
            (rightHomologyIsoCircle k ≪≫ e).hom)
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun q ↦ (overlapIntegerIso k e).inv ≫ q ≫
            (leftHomologyIsoCircle k ≪≫ e).hom)
          (productionIntersection_left_map_eq k)
          |>.trans (overlapInteger_left_component k e)
  · rw [intSignedFold_snd]
    calc
      _ = (overlapIntegerIso k e).inv ≫
          (productionIntersectionArrow leftOpen rightOpen k ≫ biprod.snd) ≫
          (rightHomologyIsoCircle k ≪≫ e).hom := by
        rw [piecesIntegerIso, biprod.mapIso_hom]
        simpa only [Category.assoc] using congrArg
          (fun q ↦ ((overlapIntegerIso k e).inv ≫
            productionIntersectionArrow leftOpen rightOpen k) ≫ q)
          (biprod.map_snd (leftHomologyIsoCircle k ≪≫ e).hom
            (rightHomologyIsoCircle k ≪≫ e).hom)
      _ = _ := by
        calc
          _ = (overlapIntegerIso k e).inv ≫
              (-(F k).map (TopCat.ofHom overlapToRight)) ≫
              (rightHomologyIsoCircle k ≪≫ e).hom := by
            simpa only [Category.assoc] using congrArg
              (fun q ↦ (overlapIntegerIso k e).inv ≫ q ≫
                (rightHomologyIsoCircle k ≪≫ e).hom)
              (productionIntersection_right_map_eq k)
          _ = _ := by
            simp only [Preadditive.comp_neg, Preadditive.neg_comp]
            exact congrArg Neg.neg (overlapInteger_right_component k e)

theorem productionIntersectionArrow_H0_conjugacy :
    (overlapIntegerIso 0 circleH0GroupIsoInt).inv ≫
        productionIntersectionArrow leftOpen rightOpen 0 ≫
        (piecesIntegerIso 0 circleH0GroupIsoInt).hom =
      intSignedFold :=
  productionIntersectionArrow_integer_conjugacy 0 circleH0GroupIsoInt

theorem productionIntersectionArrow_H1_conjugacy :
    (overlapIntegerIso 1 circleH1GroupIsoInt).inv ≫
        productionIntersectionArrow leftOpen rightOpen 1 ≫
        (piecesIntegerIso 1 circleH1GroupIsoInt).hom =
      intSignedFold :=
  productionIntersectionArrow_integer_conjugacy 1 circleH1GroupIsoInt

#print axioms left_threeFactor_eq_codiagonal
#print axioms right_threeFactor_eq_codiagonal
#print axioms overlapInteger_left_component
#print axioms overlapInteger_right_component
#print axioms productionIntersectionArrow_integer_conjugacy

end ConstructionTargets.BoundaryTorusIntegralHomology
