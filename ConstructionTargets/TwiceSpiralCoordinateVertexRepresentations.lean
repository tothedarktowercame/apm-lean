import ConstructionTargets.TwiceSpiralConnectorVertexRoundTrip

/-!
# Integer-coordinate vertex representations

This file transports connector-compatible vertex data through the supplied
twice-spiral fundamental-group coordinates.  The normalized boundary maps are
the literal `leftBoundaryHom` and `rightBoundaryHom d`.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d) (C : Type) [Groupoid C]
variable (K : LegCompatibleConnectorSystems B)

/-- Vertex representations written in the fixed integer coordinates. -/
structure CoordinateVertexData where
  leftTarget : C
  rightTarget : C
  baseGlue : leftTarget ≅ rightTarget
  leftHom : IntGroup →* End leftTarget
  rightHom : IntGroup →* End rightTarget
  boundaryCompatibility :
    baseGlue.conj.toMonoidHom.comp (leftHom.comp leftBoundaryHom) =
      rightHom.comp (rightBoundaryHom d)

/-- Intertwiners of coordinate vertex representations. -/
structure CoordinateVertexDataHom (D E : CoordinateVertexData (d := d) C) where
  left : D.leftTarget ⟶ E.leftTarget
  right : D.rightTarget ⟶ E.rightTarget
  left_intertwines : ∀ g, D.leftHom g ≫ left = left ≫ E.leftHom g
  right_intertwines : ∀ g, D.rightHom g ≫ right = right ≫ E.rightHom g
  baseGlue_square : D.baseGlue.hom ≫ right = left ≫ E.baseGlue.hom

@[ext] theorem CoordinateVertexDataHom.ext {D E : CoordinateVertexData (d := d) C}
    {f g : CoordinateVertexDataHom (d := d) C D E}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f
  cases g
  simp_all

instance : Category (CoordinateVertexData (d := d) C) where
  Hom := CoordinateVertexDataHom (d := d) C
  id D := {
    left := 𝟙 _
    right := 𝟙 _
    left_intertwines := by intro; simp
    right_intertwines := by intro; simp
    baseGlue_square := by simp }
  comp f g := {
    left := f.left ≫ g.left
    right := f.right ≫ g.right
    left_intertwines := by
      intro x
      rw [← Category.assoc, f.left_intertwines, Category.assoc,
        g.left_intertwines, ← Category.assoc]
    right_intertwines := by
      intro x
      rw [← Category.assoc, f.right_intertwines, Category.assoc,
        g.right_intertwines, ← Category.assoc]
    baseGlue_square := by
      rw [← Category.assoc, f.baseGlue_square, Category.assoc,
        g.baseGlue_square, ← Category.assoc] }
  id_comp _ := by ext <;> simp
  comp_id _ := by ext <;> simp
  assoc _ _ _ := by ext <;> simp [Category.assoc]

theorem left_leg_coordinate (x : IntPairGroup) :
    B.coordinates.leftCoord
        (coordinateLeftLeg.mapEnd _ (B.coordinates.boundaryCoord.symm x)) =
      leftBoundaryHom x := by
  simpa [leftBoundaryHom] using
    B.coordinates.left_leg (B.coordinates.boundaryCoord.symm x)

theorem right_leg_coordinate (x : IntPairGroup) :
    B.coordinates.rightCoord
        ((coordinateRightLeg h).mapEnd _ (B.coordinates.boundaryCoord.symm x)) =
      rightBoundaryHom d x := by
  simpa [rightBoundaryHom] using
    B.coordinates.right_leg (B.coordinates.boundaryCoord.symm x)

/-- Transport connector vertex data into the literal integer coordinates. -/
def toCoordinateObj (D : VertexData B C K) : CoordinateVertexData (d := d) C where
  leftTarget := D.leftTarget
  rightTarget := D.rightTarget
  baseGlue := D.baseGlue
  leftHom := D.leftHom.comp B.coordinates.leftCoord.symm.toMonoidHom
  rightHom := D.rightHom.comp B.coordinates.rightCoord.symm.toMonoidHom
  boundaryCompatibility := by
    ext x
    change D.baseGlue.conj
        (D.leftHom (B.coordinates.leftCoord.symm
          (leftBoundaryHom (Multiplicative.ofAdd x)))) =
      D.rightHom (B.coordinates.rightCoord.symm
        (rightBoundaryHom d (Multiplicative.ofAdd x)))
    have hc := DFunLike.congr_fun D.boundaryCompatibility
      (B.coordinates.boundaryCoord.symm (Multiplicative.ofAdd x))
    change D.baseGlue.conj
        (D.leftHom (coordinateLeftLeg.mapEnd _
          (B.coordinates.boundaryCoord.symm (Multiplicative.ofAdd x)))) =
      D.rightHom ((coordinateRightLeg h).mapEnd _
        (B.coordinates.boundaryCoord.symm (Multiplicative.ofAdd x))) at hc
    have hl := congrArg B.coordinates.leftCoord.symm
      (left_leg_coordinate B (Multiplicative.ofAdd x))
    have hr := congrArg B.coordinates.rightCoord.symm
      (right_leg_coordinate B (Multiplicative.ofAdd x))
    simp only [MulEquiv.symm_apply_apply] at hl hr
    rw [← hl, ← hr]
    exact hc

/-- Transport integer-coordinate data back to the supplied fundamental-group
coordinates. -/
def fromCoordinateObj (D : CoordinateVertexData (d := d) C) : VertexData B C K where
  leftTarget := D.leftTarget
  rightTarget := D.rightTarget
  baseGlue := D.baseGlue
  leftHom := D.leftHom.comp B.coordinates.leftCoord.toMonoidHom
  rightHom := D.rightHom.comp B.coordinates.rightCoord.toMonoidHom
  boundaryCompatibility := by
    ext g
    change D.baseGlue.conj
        (D.leftHom (B.coordinates.leftCoord (coordinateLeftLeg.mapEnd _ g))) =
      D.rightHom (B.coordinates.rightCoord ((coordinateRightLeg h).mapEnd _ g))
    have hc := DFunLike.congr_fun D.boundaryCompatibility
      (B.coordinates.boundaryCoord g)
    change D.baseGlue.conj
        (D.leftHom (leftBoundaryHom (B.coordinates.boundaryCoord g))) =
      D.rightHom (rightBoundaryHom d (B.coordinates.boundaryCoord g)) at hc
    have hl := left_leg_coordinate B (B.coordinates.boundaryCoord g)
    have hr := right_leg_coordinate B (B.coordinates.boundaryCoord g)
    simp only [MulEquiv.symm_apply_apply] at hl hr
    have hl' : B.coordinates.leftCoord (coordinateLeftLeg.mapEnd
        K.toCoordinateConnectorSystems.boundary.base g) =
        leftBoundaryHom (B.coordinates.boundaryCoord g) := by simpa using hl
    have hr' : B.coordinates.rightCoord ((coordinateRightLeg h).mapEnd
        K.toCoordinateConnectorSystems.boundary.base g) =
        rightBoundaryHom d (B.coordinates.boundaryCoord g) := by simpa using hr
    rw [hl', hr']
    exact hc

def toCoordinateMap {D E : VertexData B C K} (f : D ⟶ E) :
    toCoordinateObj B C K D ⟶ toCoordinateObj B C K E where
  left := f.left
  right := f.right
  left_intertwines g := f.left_intertwines (B.coordinates.leftCoord.symm g)
  right_intertwines g := f.right_intertwines (B.coordinates.rightCoord.symm g)
  baseGlue_square := f.baseGlue_square

def fromCoordinateMap {D E : CoordinateVertexData (d := d) C} (f : D ⟶ E) :
    fromCoordinateObj B C K D ⟶ fromCoordinateObj B C K E where
  left := f.left
  right := f.right
  left_intertwines g := f.left_intertwines (B.coordinates.leftCoord g)
  right_intertwines g := f.right_intertwines (B.coordinates.rightCoord g)
  baseGlue_square := f.baseGlue_square

def toCoordinateFunctor : VertexData B C K ⥤ CoordinateVertexData (d := d) C where
  obj := toCoordinateObj B C K
  map := toCoordinateMap B C K
  map_id _ := by
    apply CoordinateVertexDataHom.ext <;> rfl
  map_comp _ _ := by
    apply CoordinateVertexDataHom.ext <;> rfl

def fromCoordinateFunctor : CoordinateVertexData (d := d) C ⥤ VertexData B C K where
  obj := fromCoordinateObj B C K
  map := fromCoordinateMap B C K
  map_id _ := by
    apply VertexDataHom.ext <;> rfl
  map_comp _ _ := by
    apply VertexDataHom.ext <;> rfl

#print axioms left_leg_coordinate
#print axioms right_leg_coordinate
#print axioms toCoordinateObj
#print axioms fromCoordinateObj
#print axioms toCoordinateFunctor
#print axioms fromCoordinateFunctor

end ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
