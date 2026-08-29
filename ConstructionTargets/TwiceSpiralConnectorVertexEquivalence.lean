import ConstructionTargets.TwiceSpiralConnectorReconstructionNaturality
import ConstructionTargets.TwiceSpiralConnectorVertexRoundTrip
import ConstructionTargets.TwiceSpiralPseudococoneTransport

/-!
# Coordinate pseudococones as connector vertex data

The extraction and connector reconstruction functors are inverse up to the
two compiled natural isomorphisms.  This file verifies the remaining triangle
componentwise and composes the resulting equivalence with the collared-gluing
mapping-category equivalence.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralConnectorVertexEquivalence

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorReconstructionComparison
open ConstructionTargets.TwiceSpiralConnectorReconstructionNaturality
open ConstructionTargets.TwiceSpiralConnectorVertexData
open ConstructionTargets.TwiceSpiralConnectorVertexExtraction
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralConnectorVertexRoundTrip
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates
open ConstructionTargets.TwiceSpiralPseudococoneTransport

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d)
variable (C : Type) [Groupoid C]
variable (K : LegCompatibleConnectorSystems B)

/-- Triangle identity for extraction/reconstruction.  At each target object it
is cancellation of the mapped base connector and its inverse; neither is
identified with the identity beforehand. -/
theorem extraction_reconstruction_triangle (Q : CoordinatePseudoCocone h C) :
    (extractionFunctor B C K).map
          ((reconstructionNatIso B C K).symm.hom.app Q) ≫
        (roundTripNatIso B C K).hom.app
          ((extractionFunctor B C K).obj Q) =
      𝟙 ((extractionFunctor B C K).obj Q) := by
  apply VertexDataHom.ext
  · dsimp [reconstructionNatIso, roundTripNatIso, extractionFunctor,
      vertexDataHom, roundTripHom, roundTripIso, leftBaseComparisonIso,
      reconstructedCocone, reconstructionIso, reconstructionInv]
    change Q.left.map
          (K.toCoordinateConnectorSystems.left.connector
            K.toCoordinateConnectorSystems.left.base).inv ≫
        Q.left.map (K.toCoordinateConnectorSystems.left.normalForm
          (K.toCoordinateConnectorSystems.left.connector
            K.toCoordinateConnectorSystems.left.base).hom) = 𝟙 _
    rw [← Q.left.map_comp]
    simp [ConnectorSystem.normalForm]
  · dsimp [reconstructionNatIso, roundTripNatIso, extractionFunctor,
      vertexDataHom, roundTripHom, roundTripIso, rightBaseComparisonIso,
      reconstructedCocone, reconstructionIso, reconstructionInv]
    change Q.right.map
          (K.toCoordinateConnectorSystems.right.connector
            K.toCoordinateConnectorSystems.right.base).inv ≫
        Q.right.map (K.toCoordinateConnectorSystems.right.normalForm
          (K.toCoordinateConnectorSystems.right.connector
            K.toCoordinateConnectorSystems.right.base).hom) = 𝟙 _
    rw [← Q.right.map_comp]
    simp [ConnectorSystem.normalForm]

/-- Coordinate pseudococones are equivalent to connector-compatible
representations at the three prescribed bases. -/
def coordinatePseudoCoconeVertexDataEquivalence :
    CoordinatePseudoCocone h C ≌ VertexData B C K :=
  CategoryTheory.Equivalence.mk'
    (extractionFunctor B C K)
    (reconstructionFunctor B C K)
    (reconstructionNatIso B C K).symm
    (roundTripNatIso B C K)
    (extraction_reconstruction_triangle B C K)

@[simp] theorem coordinatePseudoCoconeVertexDataEquivalence_functor_obj
    (Q : CoordinatePseudoCocone h C) :
    (coordinatePseudoCoconeVertexDataEquivalence B C K).functor.obj Q =
      ConnectorCompatibleVertexData.ofCoordinatePseudoCocone
        B C K.toCoordinateConnectorSystems Q := rfl

@[simp] theorem coordinatePseudoCoconeVertexDataEquivalence_functor_map_left
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q) :
    ((coordinatePseudoCoconeVertexDataEquivalence B C K).functor.map τ).left =
      τ.left.app K.toCoordinateConnectorSystems.left.base := rfl

@[simp] theorem coordinatePseudoCoconeVertexDataEquivalence_functor_map_right
    {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q) :
    ((coordinatePseudoCoconeVertexDataEquivalence B C K).functor.map τ).right =
      τ.right.app K.toCoordinateConnectorSystems.right.base := rfl

/-- Connector-dependent vertex-data form of the mapping category out of the
twice-spiral gluing fundamental groupoid. -/
def gluingFundamentalGroupoidVertexDataEquivalence :
    Functor (FundamentalGroupoid (Gluing h)) C ≌ VertexData B C K :=
  (gluingFundamentalGroupoidCoordinateEquivalence h C).trans
    (coordinatePseudoCoconeVertexDataEquivalence B C K)

#print axioms extraction_reconstruction_triangle
#print axioms coordinatePseudoCoconeVertexDataEquivalence
#print axioms gluingFundamentalGroupoidVertexDataEquivalence

end ConstructionTargets.TwiceSpiralConnectorVertexEquivalence
