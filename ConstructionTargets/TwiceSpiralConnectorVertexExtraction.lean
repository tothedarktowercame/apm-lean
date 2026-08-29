import ConstructionTargets.TwiceSpiralConnectorVertexMorphisms

/-!
# Extracting connector vertex data functorially

A morphism of coordinate pseudococones restricts at the prescribed connector
bases to intertwiners of the two vertex-group representations.  Naturality at
base loops supplies the intertwining equations, while the pseudococone glue
square at the boundary base supplies compatibility with the extracted glue.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorVertexExtraction

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorVertexData
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d)
variable (C : Type) [Groupoid C]
variable (K : LegCompatibleConnectorSystems B)

/-- Extract a vertex-data morphism by evaluating the two piece natural
transformations at the prescribed connector bases. -/
def vertexDataHom {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q) :
    ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
        B C K.toCoordinateConnectorSystems P ⟶
      ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
        B C K.toCoordinateConnectorSystems Q where
  left := τ.left.app K.toCoordinateConnectorSystems.left.base
  right := τ.right.app K.toCoordinateConnectorSystems.right.base
  left_intertwines g := τ.left.naturality g
  right_intertwines g := τ.right.naturality g
  baseGlue_square := by
    have hs := congr_app τ.glue_naturality
      K.toCoordinateConnectorSystems.boundary.base
    exact hs

@[simp] theorem vertexDataHom_left {P Q : CoordinatePseudoCocone h C}
    (τ : P ⟶ Q) :
    (vertexDataHom B C K τ).left =
      τ.left.app K.toCoordinateConnectorSystems.left.base := rfl

@[simp] theorem vertexDataHom_right {P Q : CoordinatePseudoCocone h C}
    (τ : P ⟶ Q) :
    (vertexDataHom B C K τ).right =
      τ.right.app K.toCoordinateConnectorSystems.right.base := rfl

theorem vertexDataHom_left_intertwines
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q)
    (g : End K.toCoordinateConnectorSystems.left.base) :
    (ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
        B C K.toCoordinateConnectorSystems P).leftHom g ≫
        (vertexDataHom B C K τ).left =
      (vertexDataHom B C K τ).left ≫
        (ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
          B C K.toCoordinateConnectorSystems Q).leftHom g :=
  (vertexDataHom B C K τ).left_intertwines g

theorem vertexDataHom_right_intertwines
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q)
    (g : End K.toCoordinateConnectorSystems.right.base) :
    (ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
        B C K.toCoordinateConnectorSystems P).rightHom g ≫
        (vertexDataHom B C K τ).right =
      (vertexDataHom B C K τ).right ≫
        (ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
          B C K.toCoordinateConnectorSystems Q).rightHom g :=
  (vertexDataHom B C K τ).right_intertwines g

theorem vertexDataHom_baseGlue_square
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q) :
    (ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
        B C K.toCoordinateConnectorSystems P).baseGlue.hom ≫
        (vertexDataHom B C K τ).right =
      (vertexDataHom B C K τ).left ≫
        (ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
          B C K.toCoordinateConnectorSystems Q).baseGlue.hom :=
  (vertexDataHom B C K τ).baseGlue_square

/-- Functorial extraction from coordinate pseudococones to connector-compatible
vertex representations. -/
def extractionFunctor :
    CoordinatePseudoCocone h C ⥤ VertexData B C K where
  obj Q := ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
    B C K.toCoordinateConnectorSystems Q
  map τ := vertexDataHom B C K τ
  map_id Q := by
    apply VertexDataHom.ext <;> rfl
  map_comp τ υ := by
    apply VertexDataHom.ext <;> rfl

@[simp] theorem extractionFunctor_obj (Q : CoordinatePseudoCocone h C) :
    (extractionFunctor B C K).obj Q =
      ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
        B C K.toCoordinateConnectorSystems Q := rfl

@[simp] theorem extractionFunctor_map_left
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q) :
    ((extractionFunctor B C K).map τ).left =
      τ.left.app K.toCoordinateConnectorSystems.left.base := rfl

@[simp] theorem extractionFunctor_map_right
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q) :
    ((extractionFunctor B C K).map τ).right =
      τ.right.app K.toCoordinateConnectorSystems.right.base := rfl

#print axioms vertexDataHom
#print axioms extractionFunctor

end ConstructionTargets.TwiceSpiralConnectorVertexExtraction
