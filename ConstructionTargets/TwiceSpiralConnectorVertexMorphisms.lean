import ConstructionTargets.TwiceSpiralConnectorLegCompatibility

/-!
# Morphisms of connector-compatible vertex representations

Intertwiners of the two vertex representations, compatible with the base glue,
form a category.  For leg-compatible connectors, reconstruction is functorial
from this category to coordinate pseudococones.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorVertexMorphisms

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorVertexData
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d)
variable (C : Type) [Groupoid C]
variable (K : LegCompatibleConnectorSystems B)

abbrev VertexData :=
  ConnectorCompatibleVertexData B C K.toCoordinateConnectorSystems

/-- A morphism of vertex data consists of intertwiners for both vertex-group
actions and a square relating the two supplied base-glue isomorphisms. -/
structure VertexDataHom (D E : VertexData B C K) where
  left : D.leftTarget ⟶ E.leftTarget
  right : D.rightTarget ⟶ E.rightTarget
  left_intertwines : ∀ g, D.leftHom g ≫ left = left ≫ E.leftHom g
  right_intertwines : ∀ g, D.rightHom g ≫ right = right ≫ E.rightHom g
  baseGlue_square : D.baseGlue.hom ≫ right = left ≫ E.baseGlue.hom

@[ext] theorem VertexDataHom.ext {D E : VertexData B C K}
    {f g : VertexDataHom B C K D E}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f
  cases g
  simp_all

instance : Category (VertexData B C K) where
  Hom := VertexDataHom B C K
  id D := {
    left := 𝟙 D.leftTarget
    right := 𝟙 D.rightTarget
    left_intertwines := by intro g; simp
    right_intertwines := by intro g; simp
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

/-- An intertwiner of vertex representations is natural for the reconstructed
constant-object functors because every arrow is evaluated through its normal
form. -/
def leftNatTrans {D E : VertexData B C K} (f : D ⟶ E) :
    K.toCoordinateConnectorSystems.left.constantObjectFunctor
        D.leftTarget D.leftHom ⟶
      K.toCoordinateConnectorSystems.left.constantObjectFunctor
        E.leftTarget E.leftHom where
  app _ := f.left
  naturality _ _ g := f.left_intertwines
    (K.toCoordinateConnectorSystems.left.normalForm g)

/-- Right-hand analogue of `leftNatTrans`. -/
def rightNatTrans {D E : VertexData B C K} (f : D ⟶ E) :
    K.toCoordinateConnectorSystems.right.constantObjectFunctor
        D.rightTarget D.rightHom ⟶
      K.toCoordinateConnectorSystems.right.constantObjectFunctor
        E.rightTarget E.rightHom where
  app _ := f.right
  naturality _ _ g := f.right_intertwines
    (K.toCoordinateConnectorSystems.right.normalForm g)

@[simp] theorem leftNatTrans_app {D E : VertexData B C K} (f : D ⟶ E)
    (X : FundamentalGroupoid SolidTorus) : (leftNatTrans B C K f).app X = f.left := rfl

@[simp] theorem rightNatTrans_app {D E : VertexData B C K} (f : D ⟶ E)
    (X : FundamentalGroupoid SolidTorus) : (rightNatTrans B C K f).app X = f.right := rfl

/-- Reconstruction sends an intertwiner square to a morphism of coordinate
pseudococones. -/
def coordinatePseudoCoconeHom {D E : VertexData B C K} (f : D ⟶ E) :
    LegCompatibleConnectorSystems.coordinatePseudoCocone (B := B) C K D ⟶
      LegCompatibleConnectorSystems.coordinatePseudoCocone (B := B) C K E where
  left := leftNatTrans B C K f
  right := rightNatTrans B C K f
  glue_naturality := by
    ext X
    exact f.baseGlue_square

@[simp] theorem coordinatePseudoCoconeHom_left {D E : VertexData B C K}
    (f : D ⟶ E) : (coordinatePseudoCoconeHom B C K f).left = leftNatTrans B C K f := rfl

@[simp] theorem coordinatePseudoCoconeHom_right {D E : VertexData B C K}
    (f : D ⟶ E) : (coordinatePseudoCoconeHom B C K f).right = rightNatTrans B C K f := rfl

/-- Functorial reconstruction from connector-compatible vertex data to
coordinate pseudococones. -/
def reconstructionFunctor :
    VertexData B C K ⥤ CoordinatePseudoCocone h C where
  obj D := LegCompatibleConnectorSystems.coordinatePseudoCocone (B := B) C K D
  map f := coordinatePseudoCoconeHom B C K f
  map_id D := by
    apply CoordinatePseudoCoconeHom.ext
    · ext X
      rfl
    · ext X
      rfl
  map_comp f g := by
    apply CoordinatePseudoCoconeHom.ext
    · ext X
      rfl
    · ext X
      rfl

#print axioms VertexDataHom.ext
#print axioms leftNatTrans
#print axioms rightNatTrans
#print axioms coordinatePseudoCoconeHom
#print axioms reconstructionFunctor

end ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
