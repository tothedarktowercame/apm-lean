import ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
import ConstructionTargets.TwiceSpiralConnectorVertexEquivalence

/-!
# Connector vertex data in integer coordinates

The supplied solid-torus fundamental-group coordinates transport vertex data
to and from literal integer actions.  Both round trips retain the target
objects and glue isomorphism definitionally; their action homomorphisms reduce
by the inverse laws of `leftCoord` and `rightCoord`.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralCoordinateVertexEquivalence

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorVertexEquivalence
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d) (C : Type) [Groupoid C]
variable (K : LegCompatibleConnectorSystems B)

/-- The connector-data round trip is represented by identity arrows on its
literal target objects. -/
def vertexRoundTripIso (D : VertexData B C K) :
    ((toCoordinateFunctor B C K) ⋙ (fromCoordinateFunctor B C K)).obj D ≅ D where
  hom := {
    left := 𝟙 _
    right := 𝟙 _
    left_intertwines := by
      intro g
      change D.leftHom (B.coordinates.leftCoord.symm
        (B.coordinates.leftCoord g)) ≫ 𝟙 _ = 𝟙 _ ≫ D.leftHom g
      simp
    right_intertwines := by
      intro g
      change D.rightHom (B.coordinates.rightCoord.symm
        (B.coordinates.rightCoord g)) ≫ 𝟙 _ = 𝟙 _ ≫ D.rightHom g
      simp
    baseGlue_square := by
      change D.baseGlue.hom ≫ 𝟙 _ = 𝟙 _ ≫ D.baseGlue.hom
      simp }
  inv := {
    left := 𝟙 _
    right := 𝟙 _
    left_intertwines := by
      intro g
      change D.leftHom g ≫ 𝟙 _ = 𝟙 _ ≫
        D.leftHom (B.coordinates.leftCoord.symm (B.coordinates.leftCoord g))
      simp
    right_intertwines := by
      intro g
      change D.rightHom g ≫ 𝟙 _ = 𝟙 _ ≫
        D.rightHom (B.coordinates.rightCoord.symm (B.coordinates.rightCoord g))
      simp
    baseGlue_square := by
      change D.baseGlue.hom ≫ 𝟙 _ = 𝟙 _ ≫ D.baseGlue.hom
      simp }
  hom_inv_id := by
    apply VertexDataHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
  inv_hom_id := by
    apply VertexDataHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp

/-- The integer-coordinate round trip is likewise represented by identity
arrows; this time the coordinate equivalence uses `apply_symm_apply`. -/
def coordinateRoundTripIso (D : CoordinateVertexData (d := d) C) :
    ((fromCoordinateFunctor B C K) ⋙ (toCoordinateFunctor B C K)).obj D ≅ D where
  hom := {
    left := 𝟙 _
    right := 𝟙 _
    left_intertwines := by
      intro g
      change D.leftHom (B.coordinates.leftCoord
        (B.coordinates.leftCoord.symm g)) ≫ 𝟙 _ = 𝟙 _ ≫ D.leftHom g
      simp
    right_intertwines := by
      intro g
      change D.rightHom (B.coordinates.rightCoord
        (B.coordinates.rightCoord.symm g)) ≫ 𝟙 _ = 𝟙 _ ≫ D.rightHom g
      simp
    baseGlue_square := by
      change D.baseGlue.hom ≫ 𝟙 _ = 𝟙 _ ≫ D.baseGlue.hom
      simp }
  inv := {
    left := 𝟙 _
    right := 𝟙 _
    left_intertwines := by
      intro g
      change D.leftHom g ≫ 𝟙 _ = 𝟙 _ ≫
        D.leftHom (B.coordinates.leftCoord (B.coordinates.leftCoord.symm g))
      simp
    right_intertwines := by
      intro g
      change D.rightHom g ≫ 𝟙 _ = 𝟙 _ ≫
        D.rightHom (B.coordinates.rightCoord (B.coordinates.rightCoord.symm g))
      simp
    baseGlue_square := by
      change D.baseGlue.hom ≫ 𝟙 _ = 𝟙 _ ≫ D.baseGlue.hom
      simp }
  hom_inv_id := by
    apply CoordinateVertexDataHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
  inv_hom_id := by
    apply CoordinateVertexDataHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp

theorem vertexRoundTripIso_naturality {D E : VertexData B C K} (f : D ⟶ E) :
    ((toCoordinateFunctor B C K) ⋙ (fromCoordinateFunctor B C K)).map f ≫
        (vertexRoundTripIso B C K E).hom =
      (vertexRoundTripIso B C K D).hom ≫ f := by
  apply VertexDataHom.ext
  · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
  · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right; simp

theorem coordinateRoundTripIso_naturality
    {D E : CoordinateVertexData (d := d) C} (f : D ⟶ E) :
    ((fromCoordinateFunctor B C K) ⋙ (toCoordinateFunctor B C K)).map f ≫
        (coordinateRoundTripIso B C K E).hom =
      (coordinateRoundTripIso B C K D).hom ≫ f := by
  apply CoordinateVertexDataHom.ext
  · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
  · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right; simp

def vertexRoundTripNatIso :
    (toCoordinateFunctor B C K) ⋙ (fromCoordinateFunctor B C K) ≅
      𝟭 (VertexData B C K) :=
  NatIso.ofComponents (vertexRoundTripIso B C K) (by
    intro D E f
    exact vertexRoundTripIso_naturality B C K f)

def coordinateRoundTripNatIso :
    (fromCoordinateFunctor B C K) ⋙ (toCoordinateFunctor B C K) ≅
      𝟭 (CoordinateVertexData (d := d) C) :=
  NatIso.ofComponents (coordinateRoundTripIso B C K) (by
    intro D E f
    exact coordinateRoundTripIso_naturality B C K f)

theorem coordinate_vertex_triangle (D : VertexData B C K) :
    (toCoordinateFunctor B C K).map
          ((vertexRoundTripNatIso B C K).symm.hom.app D) ≫
        (coordinateRoundTripNatIso B C K).hom.app
          ((toCoordinateFunctor B C K).obj D) =
      𝟙 ((toCoordinateFunctor B C K).obj D) := by
  apply CoordinateVertexDataHom.ext
  · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
  · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp

/-- Equivalence between connector vertex representations and their literal
integer-coordinate form. -/
def vertexDataCoordinateEquivalence :
    VertexData B C K ≌ CoordinateVertexData (d := d) C :=
  CategoryTheory.Equivalence.mk'
    (toCoordinateFunctor B C K)
    (fromCoordinateFunctor B C K)
    (vertexRoundTripNatIso B C K).symm
    (coordinateRoundTripNatIso B C K)
    (coordinate_vertex_triangle B C K)

/-- Integer-coordinate mapping-category description of the twice-spiral
gluing fundamental groupoid. -/
def gluingFundamentalGroupoidCoordinateVertexEquivalence :
    Functor (FundamentalGroupoid (Gluing h)) C ≌
      CoordinateVertexData (d := d) C :=
  (gluingFundamentalGroupoidVertexDataEquivalence B C K).trans
    (vertexDataCoordinateEquivalence B C K)

#print axioms vertexRoundTripIso
#print axioms coordinateRoundTripIso
#print axioms vertexRoundTripNatIso
#print axioms coordinateRoundTripNatIso
#print axioms vertexDataCoordinateEquivalence
#print axioms gluingFundamentalGroupoidCoordinateVertexEquivalence

end ConstructionTargets.TwiceSpiralCoordinateVertexEquivalence
