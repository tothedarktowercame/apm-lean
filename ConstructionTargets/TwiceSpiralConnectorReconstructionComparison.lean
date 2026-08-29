import ConstructionTargets.TwiceSpiralConnectorVertexExtraction

/-!
# Comparing connector reconstruction with a coordinate pseudococone

The chosen connectors give natural isomorphisms from the constant-object
reconstruction of a coordinate pseudococone's vertex representations back to
its original piece functors.  Their overlap square is the naturality square of
the original glue at the chosen boundary connector.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorReconstructionComparison

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorVertexData
open ConstructionTargets.TwiceSpiralConnectorVertexExtraction
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d)
variable (C : Type) [Groupoid C]
variable (K : LegCompatibleConnectorSystems B)

abbrev reconstructed (Q : CoordinatePseudoCocone h C) :
    CoordinatePseudoCocone h C :=
  (reconstructionFunctor B C K).obj ((extractionFunctor B C K).obj Q)

/-- Connector normal-form reconstruction, mapped through an arbitrary
groupoid functor. -/
theorem map_normalForm_comp_connector
    (F : FundamentalGroupoid SolidTorus ⥤ C)
    (S : ConnectorSystem (FundamentalGroupoid SolidTorus))
    {X Y : FundamentalGroupoid SolidTorus} (f : X ⟶ Y) :
    F.map (S.normalForm f) ≫ F.map (S.connector Y).hom =
      F.map (S.connector X).hom ≫ F.map f := by
  rw [← F.map_comp, ← F.map_comp]
  apply congrArg F.map
  simp [ConnectorSystem.normalForm, Category.assoc]

/-- The reconstructed left constant-object functor is naturally isomorphic to
the original left piece functor.  The base connector is not normalized. -/
def leftReconstructionIso (Q : CoordinatePseudoCocone h C) :
    (reconstructed B C K Q).left ≅ Q.left :=
  NatIso.ofComponents
    (fun X => Q.left.mapIso (K.toCoordinateConnectorSystems.left.connector X))
    (by
      intro X Y f
      exact map_normalForm_comp_connector C Q.left
        K.toCoordinateConnectorSystems.left f)

/-- Right-hand analogue of `leftReconstructionIso`. -/
def rightReconstructionIso (Q : CoordinatePseudoCocone h C) :
    (reconstructed B C K Q).right ≅ Q.right :=
  NatIso.ofComponents
    (fun X => Q.right.mapIso (K.toCoordinateConnectorSystems.right.connector X))
    (by
      intro X Y f
      exact map_normalForm_comp_connector C Q.right
        K.toCoordinateConnectorSystems.right f)

@[simp] theorem leftReconstructionIso_hom_app
    (Q : CoordinatePseudoCocone h C) (X : FundamentalGroupoid SolidTorus) :
    (leftReconstructionIso B C K Q).hom.app X =
      Q.left.map (K.toCoordinateConnectorSystems.left.connector X).hom := rfl

@[simp] theorem rightReconstructionIso_hom_app
    (Q : CoordinatePseudoCocone h C) (X : FundamentalGroupoid SolidTorus) :
    (rightReconstructionIso B C K Q).hom.app X =
      Q.right.map (K.toCoordinateConnectorSystems.right.connector X).hom := rfl

/-- The two connector comparison isomorphisms respect the overlap glue.  This
is exactly `Q.glue.hom.naturality` at the boundary connector, after applying
the two leg-compatibility equations. -/
theorem reconstruction_glue_square (Q : CoordinatePseudoCocone h C) :
    (reconstructed B C K Q).glue.hom ≫
        Functor.whiskerLeft (coordinateRightLeg h)
          (rightReconstructionIso B C K Q).hom =
      Functor.whiskerLeft coordinateLeftLeg
          (leftReconstructionIso B C K Q).hom ≫ Q.glue.hom := by
  ext X
  change (B.glueBaseIso Q).hom ≫
      Q.right.map (K.rightConnector ((coordinateRightLeg h).obj X)).hom =
    Q.left.map (K.leftConnector (coordinateLeftLeg.obj X)).hom ≫ Q.glue.hom.app X
  rw [← K.left_connector_map X, ← K.right_connector_map X]
  simpa using (Q.glue.hom.naturality (K.boundaryConnector X).hom).symm

/-- The forward pseudococone comparison from reconstruction after extraction
to the original coordinate pseudococone. -/
def reconstructionHom (Q : CoordinatePseudoCocone h C) :
    reconstructed B C K Q ⟶ Q where
  left := (leftReconstructionIso B C K Q).hom
  right := (rightReconstructionIso B C K Q).hom
  glue_naturality := reconstruction_glue_square B C K Q

theorem inverse_square {A A' Z Z' : C} (l : A ≅ A') (r : Z ≅ Z')
    (a : A ⟶ Z) (b : A' ⟶ Z') (hs : a ≫ r.hom = l.hom ≫ b) :
    b ≫ r.inv = l.inv ≫ a := by
  rw [← cancel_epi l.hom]
  rw [← Category.assoc]
  rw [← hs]
  simp

/-- The inverse glue square follows by cancelling the four isomorphism
components in the forward square. -/
theorem reconstruction_glue_square_inv (Q : CoordinatePseudoCocone h C) :
    Q.glue.hom ≫ Functor.whiskerLeft (coordinateRightLeg h)
        (rightReconstructionIso B C K Q).inv =
      Functor.whiskerLeft coordinateLeftLeg
          (leftReconstructionIso B C K Q).inv ≫
        (reconstructed B C K Q).glue.hom := by
  ext X
  change Q.glue.hom.app X ≫
      (rightReconstructionIso B C K Q).inv.app ((coordinateRightLeg h).obj X) =
    (leftReconstructionIso B C K Q).inv.app (coordinateLeftLeg.obj X) ≫
      (reconstructed B C K Q).glue.hom.app X
  have hs := NatTrans.congr_app (reconstruction_glue_square B C K Q) X
  change (reconstructed B C K Q).glue.hom.app X ≫
      (rightReconstructionIso B C K Q).hom.app ((coordinateRightLeg h).obj X) =
    (leftReconstructionIso B C K Q).hom.app (coordinateLeftLeg.obj X) ≫
      Q.glue.hom.app X at hs
  exact inverse_square C
    ((leftReconstructionIso B C K Q).app (coordinateLeftLeg.obj X))
    ((rightReconstructionIso B C K Q).app ((coordinateRightLeg h).obj X))
    ((reconstructed B C K Q).glue.hom.app X) (Q.glue.hom.app X) hs

/-- Inverse pseudococone comparison. -/
def reconstructionInv (Q : CoordinatePseudoCocone h C) :
    Q ⟶ reconstructed B C K Q where
  left := (leftReconstructionIso B C K Q).inv
  right := (rightReconstructionIso B C K Q).inv
  glue_naturality := reconstruction_glue_square_inv B C K Q

/-- Reconstruction after extraction is isomorphic to the original coordinate
pseudococone, without normalizing any base connector. -/
def reconstructionIso (Q : CoordinatePseudoCocone h C) :
    reconstructed B C K Q ≅ Q where
  hom := reconstructionHom B C K Q
  inv := reconstructionInv B C K Q
  hom_inv_id := by
    apply CoordinatePseudoCoconeHom.ext
    · exact (leftReconstructionIso B C K Q).hom_inv_id
    · exact (rightReconstructionIso B C K Q).hom_inv_id
  inv_hom_id := by
    apply CoordinatePseudoCoconeHom.ext
    · exact (leftReconstructionIso B C K Q).inv_hom_id
    · exact (rightReconstructionIso B C K Q).inv_hom_id

#print axioms map_normalForm_comp_connector
#print axioms leftReconstructionIso
#print axioms rightReconstructionIso
#print axioms reconstruction_glue_square
#print axioms reconstructionHom
#print axioms reconstructionInv
#print axioms reconstructionIso

end ConstructionTargets.TwiceSpiralConnectorReconstructionComparison
