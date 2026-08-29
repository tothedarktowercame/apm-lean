import ConstructionTargets.ConnectedGroupoidVertexReconstruction
import ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction

/-!
# Connector-compatible vertex data for the twice-spiral span

This file records explicit connector systems on the three coordinate
groupoids and extracts the vertex-group representation carried by a coordinate
pseudococone.  The compatibility equation is the component of the cocone glue
at the chosen boundary base object.
-/

open CategoryTheory
open scoped FundamentalGroupoid

noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorVertexData

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates
open ConstructionTargets.TwiceSpiralPseudococoneTransport

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d)
variable (C : Type) [Groupoid C]

/-- Connector systems on the boundary and the two (differently based)
solid-torus coordinate groupoids.  The bases are fixed definitionally, so no
basepoint cast is hidden in the extracted vertex homomorphisms. -/
structure CoordinateConnectorSystems where
  boundaryConnector : ∀ X : FundamentalGroupoid BoundaryTorus,
    FundamentalGroupoid.mk B.boundaryBase ≅ X
  leftConnector : ∀ X : FundamentalGroupoid SolidTorus,
    FundamentalGroupoid.mk B.leftBase ≅ X
  rightConnector : ∀ X : FundamentalGroupoid SolidTorus,
    FundamentalGroupoid.mk B.rightBase ≅ X

namespace CoordinateConnectorSystems

/-- The boundary connector system with the prescribed base. -/
def boundary (K : CoordinateConnectorSystems B) :
    ConnectorSystem (FundamentalGroupoid BoundaryTorus) :=
  ⟨FundamentalGroupoid.mk B.boundaryBase, K.boundaryConnector⟩

/-- The left solid-torus connector system with the prescribed base. -/
def left (K : CoordinateConnectorSystems B) :
    ConnectorSystem (FundamentalGroupoid SolidTorus) :=
  ⟨FundamentalGroupoid.mk B.leftBase, K.leftConnector⟩

/-- The right solid-torus connector system with the prescribed base. -/
def right (K : CoordinateConnectorSystems B) :
    ConnectorSystem (FundamentalGroupoid SolidTorus) :=
  ⟨FundamentalGroupoid.mk B.rightBase, K.rightConnector⟩

end CoordinateConnectorSystems

/-- Vertex-group representation data at the three chosen connector bases.
The boundary compatibility retains the actual conjugation by the glue
isomorphism between the two target base objects. -/
structure ConnectorCompatibleVertexData
    (K : CoordinateConnectorSystems B) where
  leftTarget : C
  rightTarget : C
  baseGlue : leftTarget ≅ rightTarget
  leftHom : End K.left.base →* End leftTarget
  rightHom : End K.right.base →* End rightTarget
  boundaryCompatibility :
    baseGlue.conj.toMonoidHom.comp
        (leftHom.comp (coordinateLeftLeg.mapEnd K.boundary.base)) =
      rightHom.comp ((coordinateRightLeg h).mapEnd K.boundary.base)

namespace ConnectorCompatibleVertexData

/-- Extract connector-based vertex representation data from a coordinate
pseudococone.  Connector choices do not affect this forward extraction: they
become relevant when extending the vertex representations back to functors. -/
def ofCoordinatePseudoCocone (K : CoordinateConnectorSystems B)
    (Q : CoordinatePseudoCocone h C) : ConnectorCompatibleVertexData B C K where
  leftTarget := Q.left.obj K.left.base
  rightTarget := Q.right.obj K.right.base
  baseGlue := B.glueBaseIso Q
  leftHom := B.leftAutomorphismHom Q
  rightHom := B.rightAutomorphismHom Q
  boundaryCompatibility := B.boundaryRestrictions_conjugate_hom Q

@[simp] theorem ofCoordinatePseudoCocone_leftTarget
    (K : CoordinateConnectorSystems B) (Q : CoordinatePseudoCocone h C) :
    (ofCoordinatePseudoCocone B C K Q).leftTarget = Q.left.obj K.left.base := rfl

@[simp] theorem ofCoordinatePseudoCocone_rightTarget
    (K : CoordinateConnectorSystems B) (Q : CoordinatePseudoCocone h C) :
    (ofCoordinatePseudoCocone B C K Q).rightTarget = Q.right.obj K.right.base := rfl

@[simp] theorem ofCoordinatePseudoCocone_baseGlue
    (K : CoordinateConnectorSystems B) (Q : CoordinatePseudoCocone h C) :
    (ofCoordinatePseudoCocone B C K Q).baseGlue = B.glueBaseIso Q := rfl

@[simp] theorem ofCoordinatePseudoCocone_leftHom
    (K : CoordinateConnectorSystems B) (Q : CoordinatePseudoCocone h C) :
    (ofCoordinatePseudoCocone B C K Q).leftHom = B.leftAutomorphismHom Q := rfl

@[simp] theorem ofCoordinatePseudoCocone_rightHom
    (K : CoordinateConnectorSystems B) (Q : CoordinatePseudoCocone h C) :
    (ofCoordinatePseudoCocone B C K Q).rightHom = B.rightAutomorphismHom Q := rfl

/-- The extracted compatibility proof has exactly the homomorphism equation
proved by `PointedCoordinateBases.boundaryRestrictions_conjugate_hom`. -/
theorem ofCoordinatePseudoCocone_boundaryCompatibility
    (K : CoordinateConnectorSystems B) (Q : CoordinatePseudoCocone h C) :
    (ofCoordinatePseudoCocone B C K Q).baseGlue.conj.toMonoidHom.comp
        ((ofCoordinatePseudoCocone B C K Q).leftHom.comp
          (coordinateLeftLeg.mapEnd K.boundary.base)) =
      (ofCoordinatePseudoCocone B C K Q).rightHom.comp
        ((coordinateRightLeg h).mapEnd K.boundary.base) :=
  B.boundaryRestrictions_conjugate_hom Q

end ConnectorCompatibleVertexData

#print axioms CoordinateConnectorSystems.boundary
#print axioms CoordinateConnectorSystems.left
#print axioms CoordinateConnectorSystems.right
#print axioms ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
#print axioms ConnectorCompatibleVertexData.ofCoordinatePseudoCocone_boundaryCompatibility

end ConstructionTargets.TwiceSpiralConnectorVertexData
