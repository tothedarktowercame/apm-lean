import ConstructionTargets.TwiceSpiralConnectorVertexData

/-!
# Connector compatibility with the twice-spiral span legs

This file records that the chosen boundary connectors map to the chosen piece
connectors and uses that coherence to reconstruct the overlap naturality
square from the vertex-group compatibility equation.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorLegCompatibility

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorVertexData
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d)
variable (C : Type) [Groupoid C]

/-- Connector systems whose piece connectors are literally the images of the
chosen boundary connectors under the two coordinate span legs. -/
structure LegCompatibleConnectorSystems extends CoordinateConnectorSystems B where
  left_connector_map : ∀ X : FundamentalGroupoid BoundaryTorus,
    coordinateLeftLeg.mapIso (toCoordinateConnectorSystems.boundaryConnector X) =
      toCoordinateConnectorSystems.leftConnector (coordinateLeftLeg.obj X)
  right_connector_map : ∀ X : FundamentalGroupoid BoundaryTorus,
    (coordinateRightLeg h).mapIso
        (toCoordinateConnectorSystems.boundaryConnector X) =
      toCoordinateConnectorSystems.rightConnector ((coordinateRightLeg h).obj X)

namespace LegCompatibleConnectorSystems

variable (K : LegCompatibleConnectorSystems B)

theorem left_normalForm_map {X Y : FundamentalGroupoid BoundaryTorus}
    (f : X ⟶ Y) :
    K.toCoordinateConnectorSystems.left.normalForm (coordinateLeftLeg.map f) =
      coordinateLeftLeg.map
        (K.toCoordinateConnectorSystems.boundary.normalForm f) := by
  simp only [ConnectorSystem.normalForm]
  change (K.leftConnector (coordinateLeftLeg.obj X)).hom ≫
      coordinateLeftLeg.map f ≫
        (K.leftConnector (coordinateLeftLeg.obj Y)).inv =
    coordinateLeftLeg.map ((K.boundaryConnector X).hom ≫ f ≫
      (K.boundaryConnector Y).inv)
  rw [← K.left_connector_map X, ← K.left_connector_map Y]
  simp
  rfl

theorem right_normalForm_map {X Y : FundamentalGroupoid BoundaryTorus}
    (f : X ⟶ Y) :
    K.toCoordinateConnectorSystems.right.normalForm ((coordinateRightLeg h).map f) =
      (coordinateRightLeg h).map
        (K.toCoordinateConnectorSystems.boundary.normalForm f) := by
  simp only [ConnectorSystem.normalForm]
  change (K.rightConnector ((coordinateRightLeg h).obj X)).hom ≫
      (coordinateRightLeg h).map f ≫
        (K.rightConnector ((coordinateRightLeg h).obj Y)).inv =
    (coordinateRightLeg h).map ((K.boundaryConnector X).hom ≫ f ≫
      (K.boundaryConnector Y).inv)
  rw [← K.right_connector_map X, ← K.right_connector_map Y]
  simp
  rfl

/-- Vertex-group compatibility reconstructs the naturality equation for every
boundary morphism between the two constant-object representation functors. -/
theorem constantFunctor_boundary_naturality
    (D : ConnectorCompatibleVertexData B C K.toCoordinateConnectorSystems)
    {X Y : FundamentalGroupoid BoundaryTorus} (f : X ⟶ Y) :
    (K.toCoordinateConnectorSystems.left.constantObjectFunctor
        D.leftTarget D.leftHom).map (coordinateLeftLeg.map f) ≫ D.baseGlue.hom =
      D.baseGlue.hom ≫
        (K.toCoordinateConnectorSystems.right.constantObjectFunctor
          D.rightTarget D.rightHom).map ((coordinateRightLeg h).map f) := by
  rw [ConnectorSystem.constantObjectFunctor_map,
    ConnectorSystem.constantObjectFunctor_map,
    K.left_normalForm_map, K.right_normalForm_map]
  have hc := D.boundaryCompatibility
  have hp := DFunLike.congr_fun hc
    (K.toCoordinateConnectorSystems.boundary.normalForm f)
  change D.baseGlue.inv ≫
      D.leftHom (coordinateLeftLeg.map
        (K.toCoordinateConnectorSystems.boundary.normalForm f)) ≫
      D.baseGlue.hom =
    D.rightHom ((coordinateRightLeg h).map
      (K.toCoordinateConnectorSystems.boundary.normalForm f)) at hp
  apply D.baseGlue.inv_comp_eq.mp
  simpa only [Category.assoc] using hp

/-- The overlap isomorphism reconstructed from the compatible vertex-group
representations.  Its components are all the supplied base isomorphism; the
naturality proof is the normal-form calculation above. -/
def constantGlueNatIso
    (D : ConnectorCompatibleVertexData B C K.toCoordinateConnectorSystems) :
    coordinateLeftLeg ⋙
        K.toCoordinateConnectorSystems.left.constantObjectFunctor
          D.leftTarget D.leftHom ≅
      coordinateRightLeg h ⋙
        K.toCoordinateConnectorSystems.right.constantObjectFunctor
          D.rightTarget D.rightHom :=
  NatIso.ofComponents (fun _ => D.baseGlue) (by
    intro X Y f
    exact constantFunctor_boundary_naturality (B := B) C K D f)

/-- A compatible pair of vertex-group representations reconstructs an honest
coordinate pseudococone once the connector systems commute with both legs. -/
def coordinatePseudoCocone
    (D : ConnectorCompatibleVertexData B C K.toCoordinateConnectorSystems) :
    CoordinatePseudoCocone h C where
  left := K.toCoordinateConnectorSystems.left.constantObjectFunctor
    D.leftTarget D.leftHom
  right := K.toCoordinateConnectorSystems.right.constantObjectFunctor
    D.rightTarget D.rightHom
  glue := constantGlueNatIso (B := B) C K D

#print axioms left_normalForm_map
#print axioms right_normalForm_map
#print axioms constantFunctor_boundary_naturality
#print axioms constantGlueNatIso
#print axioms coordinatePseudoCocone

end LegCompatibleConnectorSystems

end ConstructionTargets.TwiceSpiralConnectorLegCompatibility
