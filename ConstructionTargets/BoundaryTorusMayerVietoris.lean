import ConstructionTargets.BoundaryTorusOpenCover
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.CircleHomology

/-!
# Homology coordinates for the boundary-torus open cover

This first Mayer--Vietoris packet transports the two pieces to the circle and
the overlap to the disjoint union of two circles.  It also records the circle
coordinates and the literal component fold map that the inclusion comparison
must identify.  It does not assume a coproduct-homology theorem or an
inclusion matrix.
-/

open Set Topology CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.BoundaryTorusMayerVietoris

open ConstructionTargets.BoundaryTorusOpenCover
open ConstructionTargets.CircleHomology
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SphereHomology
open ConstructionTargets.ProductionOpenCoverMayerVietoris

abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

noncomputable def circleHomologyIsoSphereOne (k : ℕ) :
    H k Circle ≅ GroupHomology 1 k :=
  singularHomologyIsoOfHomotopyEquiv
    circleHomeomorphSphereOne.toHomotopyEquiv k

noncomputable def circleH0GroupIsoInt :
    H 0 Circle ≅ AddCommGrpCat.of ℤ :=
  circleHomologyIsoSphereOne 0 ≪≫ sphereH0IsoInt 1 one_pos

noncomputable def circleH1GroupIsoInt :
    H 1 Circle ≅ AddCommGrpCat.of ℤ :=
  circleHomologyIsoSphereOne 1 ≪≫ sphereTopHomologyIsoInt 1 one_pos

theorem circleHomology_isZero_of_one_lt (k : ℕ) (hk : 1 < k) :
    IsZero (H k Circle) :=
  (sphereHomology_isZero_of_gt 1 k hk).of_iso
    (circleHomologyIsoSphereOne k)

noncomputable def leftHomologyIsoCircle (k : ℕ) :
    H k leftOpen ≅ H k Circle :=
  singularHomologyIsoOfHomotopyEquiv leftOpenHomotopyEquivCircle k

noncomputable def rightHomologyIsoCircle (k : ℕ) :
    H k rightOpen ≅ H k Circle :=
  singularHomologyIsoOfHomotopyEquiv rightOpenHomotopyEquivCircle k

noncomputable def leftH0IsoInt : H 0 leftOpen ≅ AddCommGrpCat.of ℤ :=
  leftHomologyIsoCircle 0 ≪≫ circleH0GroupIsoInt

noncomputable def rightH0IsoInt : H 0 rightOpen ≅ AddCommGrpCat.of ℤ :=
  rightHomologyIsoCircle 0 ≪≫ circleH0GroupIsoInt

noncomputable def leftH1IsoInt : H 1 leftOpen ≅ AddCommGrpCat.of ℤ :=
  leftHomologyIsoCircle 1 ≪≫ circleH1GroupIsoInt

noncomputable def rightH1IsoInt : H 1 rightOpen ≅ AddCommGrpCat.of ℤ :=
  rightHomologyIsoCircle 1 ≪≫ circleH1GroupIsoInt

theorem leftHomology_isZero_of_one_lt (k : ℕ) (hk : 1 < k) :
    IsZero (H k leftOpen) :=
  (circleHomology_isZero_of_one_lt k hk).of_iso (leftHomologyIsoCircle k)

theorem rightHomology_isZero_of_one_lt (k : ℕ) (hk : 1 < k) :
    IsZero (H k rightOpen) :=
  (circleHomology_isZero_of_one_lt k hk).of_iso (rightHomologyIsoCircle k)

noncomputable def overlapHomologyIsoTwoCircles (k : ℕ) :
    H k Overlap ≅ H k (Circle ⊕ Circle) :=
  singularHomologyIsoOfHomotopyEquiv overlapHomotopyEquivTwoCircles k

/-- Both connected components retain the first circle coordinate.  This is
the continuous map whose induced homology map must occur in each geometric
inclusion square. -/
def twoCircleFold : C(Circle ⊕ Circle, Circle) :=
  ⟨Sum.elim id id, continuous_id.sumElim continuous_id⟩

@[simp] theorem twoCircleFold_inl (z : Circle) :
    twoCircleFold (Sum.inl z) = z := rfl

@[simp] theorem twoCircleFold_inr (z : Circle) :
    twoCircleFold (Sum.inr z) = z := rfl

/-- The inverse half of the overlap equivalence, retained as a named
continuous map for the inclusion-coordinate comparison. -/
def twoCirclesToOverlap : C(Circle ⊕ Circle, Overlap) :=
  overlapHomotopyEquivTwoCircles.invFun

def overlapToLeft : C(Overlap, leftOpen) :=
  ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

def overlapToRight : C(Overlap, rightOpen) :=
  ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

def leftPieceRetraction : C(leftOpen, Circle) :=
  leftOpenHomotopyEquivCircle.toFun

def rightPieceRetraction : C(rightOpen, Circle) :=
  rightOpenHomotopyEquivCircle.toFun

def leftOverlapComposite : C(Circle ⊕ Circle, Circle) :=
  leftPieceRetraction.comp (overlapToLeft.comp twoCirclesToOverlap)

def rightOverlapComposite : C(Circle ⊕ Circle, Circle) :=
  rightPieceRetraction.comp (overlapToRight.comp twoCirclesToOverlap)

theorem leftOverlapComposite_eq_fold :
    leftOverlapComposite = twoCircleFold := by
  ext x
  rcases x with x | x <;> rfl

theorem rightOverlapComposite_eq_fold :
    rightOverlapComposite = twoCircleFold := by
  ext x
  rcases x with x | x <;> rfl

@[simp] theorem leftOverlapComposite_inl (z : Circle) :
    leftOverlapComposite (Sum.inl z) = z := by
  rw [leftOverlapComposite_eq_fold]
  rfl

@[simp] theorem leftOverlapComposite_inr (z : Circle) :
    leftOverlapComposite (Sum.inr z) = z := by
  rw [leftOverlapComposite_eq_fold]
  rfl

@[simp] theorem rightOverlapComposite_inl (z : Circle) :
    rightOverlapComposite (Sum.inl z) = z := by
  rw [rightOverlapComposite_eq_fold]
  rfl

@[simp] theorem rightOverlapComposite_inr (z : Circle) :
    rightOverlapComposite (Sum.inr z) = z := by
  rw [rightOverlapComposite_eq_fold]
  rfl

theorem leftOverlapComposite_homologyMap (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom leftOverlapComposite) =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom twoCircleFold) := by
  rw [leftOverlapComposite_eq_fold]

theorem rightOverlapComposite_homologyMap (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom rightOverlapComposite) =
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom twoCircleFold) := by
  rw [rightOverlapComposite_eq_fold]

#print axioms circleH0GroupIsoInt
#print axioms circleH1GroupIsoInt
#print axioms leftH1IsoInt
#print axioms overlapHomologyIsoTwoCircles
#print axioms twoCircleFold_inl
#print axioms leftOverlapComposite_eq_fold
#print axioms rightOverlapComposite_eq_fold
#print axioms leftOverlapComposite_homologyMap

end ConstructionTargets.BoundaryTorusMayerVietoris
