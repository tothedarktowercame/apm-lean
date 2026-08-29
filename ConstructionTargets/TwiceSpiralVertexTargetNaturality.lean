import ConstructionTargets.TwiceSpiralPushoutTargetNaturality
import ConstructionTargets.TwiceSpiralCoordinateVertexEquivalence
import Mathlib.CategoryTheory.Conj

/-!
# Target postcomposition for connector vertex data

This file proves that changing the target groupoid commutes with transport
through the fixed fundamental-group coordinates.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralVertexTargetNaturality

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates
open ConstructionTargets.TwiceSpiralPushoutTargetNaturality

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d) (K : LegCompatibleConnectorSystems B)
variable {C D : Type} [Groupoid C] [Groupoid D]

/-- Apply a target functor to connector-compatible vertex data. -/
def postcomposeVertexDataObj (H : C ⥤ D) (R : VertexData B C K) :
    VertexData B D K where
  leftTarget := H.obj R.leftTarget
  rightTarget := H.obj R.rightTarget
  baseGlue := H.mapIso R.baseGlue
  leftHom := {
    toFun := fun g => H.map (R.leftHom g)
    map_one' := by rw [R.leftHom.map_one]; exact H.map_id _
    map_mul' := by intro x y; rw [R.leftHom.map_mul]; exact H.map_comp _ _ }
  rightHom := {
    toFun := fun g => H.map (R.rightHom g)
    map_one' := by rw [R.rightHom.map_one]; exact H.map_id _
    map_mul' := by intro x y; rw [R.rightHom.map_mul]; exact H.map_comp _ _ }
  boundaryCompatibility := by
    ext x
    have hx := DFunLike.congr_fun R.boundaryCompatibility x
    exact (H.map_conj R.baseGlue
      (R.leftHom (coordinateLeftLeg.mapEnd _ x))).symm.trans (congrArg H.map hx)

def postcomposeVertexDataMap (H : C ⥤ D) {R S : VertexData B C K} (f : R ⟶ S) :
    postcomposeVertexDataObj B K H R ⟶ postcomposeVertexDataObj B K H S where
  left := H.map f.left
  right := H.map f.right
  left_intertwines g := by
    change H.map (R.leftHom g) ≫ H.map f.left =
      H.map f.left ≫ H.map (S.leftHom g)
    rw [← H.map_comp, ← H.map_comp, f.left_intertwines]
  right_intertwines g := by
    change H.map (R.rightHom g) ≫ H.map f.right =
      H.map f.right ≫ H.map (S.rightHom g)
    rw [← H.map_comp, ← H.map_comp, f.right_intertwines]
  baseGlue_square := by
    change H.map R.baseGlue.hom ≫ H.map f.right =
      H.map f.left ≫ H.map S.baseGlue.hom
    rw [← H.map_comp, ← H.map_comp, f.baseGlue_square]

def postcomposeVertexDataFunctor (H : C ⥤ D) : VertexData B C K ⥤ VertexData B D K where
  obj := postcomposeVertexDataObj B K H
  map := postcomposeVertexDataMap B K H
  map_id R := by apply VertexDataHom.ext <;> exact H.map_id _
  map_comp f g := by apply VertexDataHom.ext <;> exact H.map_comp _ _

/-- Coordinate transport commutes with target postcomposition. -/
def toCoordinatePostcomposeIso (H : C ⥤ D) :
    postcomposeVertexDataFunctor B K H ⋙ toCoordinateFunctor B D K ≅
      toCoordinateFunctor B C K ⋙ postcomposeCoordinateVertexFunctor H :=
  NatIso.ofComponents (fun R => {
    hom := {
      left := 𝟙 _
      right := 𝟙 _
      left_intertwines := by intro g; change
        (H.map (R.leftHom (B.coordinates.leftCoord.symm g)) ≫ 𝟙 _) =
          (𝟙 _ ≫ H.map (R.leftHom (B.coordinates.leftCoord.symm g))); simp
      right_intertwines := by intro g; change
        (H.map (R.rightHom (B.coordinates.rightCoord.symm g)) ≫ 𝟙 _) =
          (𝟙 _ ≫ H.map (R.rightHom (B.coordinates.rightCoord.symm g))); simp
      baseGlue_square := by change (H.map R.baseGlue.hom ≫ 𝟙 _) =
        (𝟙 _ ≫ H.map R.baseGlue.hom); simp }
    inv := {
      left := 𝟙 _
      right := 𝟙 _
      left_intertwines := by intro g; change
        (H.map (R.leftHom (B.coordinates.leftCoord.symm g)) ≫ 𝟙 _) =
          (𝟙 _ ≫ H.map (R.leftHom (B.coordinates.leftCoord.symm g))); simp
      right_intertwines := by intro g; change
        (H.map (R.rightHom (B.coordinates.rightCoord.symm g)) ≫ 𝟙 _) =
          (𝟙 _ ≫ H.map (R.rightHom (B.coordinates.rightCoord.symm g))); simp
      baseGlue_square := by change (H.map R.baseGlue.hom ≫ 𝟙 _) =
        (𝟙 _ ≫ H.map R.baseGlue.hom); simp }
    hom_inv_id := by apply CoordinateVertexDataHom.ext <;>
      change (𝟙 _ ≫ 𝟙 _) = 𝟙 _ <;> simp
    inv_hom_id := by apply CoordinateVertexDataHom.ext <;>
      change (𝟙 _ ≫ 𝟙 _) = 𝟙 _ <;> simp }) (by
        intro R S f
        apply CoordinateVertexDataHom.ext
        · change H.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ H.map f.left; simp
        · change H.map f.right ≫ 𝟙 _ = 𝟙 _ ≫ H.map f.right; simp)

/-- The reverse coordinate transport also commutes with target
postcomposition. -/
def fromCoordinatePostcomposeIso (H : C ⥤ D) :
    postcomposeCoordinateVertexFunctor (d := d) H ⋙ fromCoordinateFunctor B D K ≅
      fromCoordinateFunctor B C K ⋙ postcomposeVertexDataFunctor B K H :=
  NatIso.ofComponents (fun R => {
    hom := {
      left := 𝟙 _
      right := 𝟙 _
      left_intertwines := by intro g; change
        (H.map (R.leftHom (B.coordinates.leftCoord g)) ≫ 𝟙 _) =
          (𝟙 _ ≫ H.map (R.leftHom (B.coordinates.leftCoord g))); simp
      right_intertwines := by intro g; change
        (H.map (R.rightHom (B.coordinates.rightCoord g)) ≫ 𝟙 _) =
          (𝟙 _ ≫ H.map (R.rightHom (B.coordinates.rightCoord g))); simp
      baseGlue_square := by change (H.map R.baseGlue.hom ≫ 𝟙 _) =
        (𝟙 _ ≫ H.map R.baseGlue.hom); simp }
    inv := {
      left := 𝟙 _
      right := 𝟙 _
      left_intertwines := by intro g; change
        (H.map (R.leftHom (B.coordinates.leftCoord g)) ≫ 𝟙 _) =
          (𝟙 _ ≫ H.map (R.leftHom (B.coordinates.leftCoord g))); simp
      right_intertwines := by intro g; change
        (H.map (R.rightHom (B.coordinates.rightCoord g)) ≫ 𝟙 _) =
          (𝟙 _ ≫ H.map (R.rightHom (B.coordinates.rightCoord g))); simp
      baseGlue_square := by change (H.map R.baseGlue.hom ≫ 𝟙 _) =
        (𝟙 _ ≫ H.map R.baseGlue.hom); simp }
    hom_inv_id := by apply VertexDataHom.ext <;>
      change (𝟙 _ ≫ 𝟙 _) = 𝟙 _ <;> simp
    inv_hom_id := by apply VertexDataHom.ext <;>
      change (𝟙 _ ≫ 𝟙 _) = 𝟙 _ <;> simp }) (by
        intro R S f
        apply VertexDataHom.ext
        · change H.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ H.map f.left; simp
        · change H.map f.right ≫ 𝟙 _ = 𝟙 _ ≫ H.map f.right; simp)

#print axioms postcomposeVertexDataFunctor
#print axioms toCoordinatePostcomposeIso
#print axioms fromCoordinatePostcomposeIso

end ConstructionTargets.TwiceSpiralVertexTargetNaturality
