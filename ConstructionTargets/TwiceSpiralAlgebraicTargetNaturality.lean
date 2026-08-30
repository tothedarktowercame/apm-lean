import ConstructionTargets.TwiceSpiralVertexTargetNaturality
import ConstructionTargets.TwiceSpiralPushoutRepresentationRoundTrip
import ConstructionTargets.TwiceSpiralPushoutSingleObjEquivalence
import Mathlib.CategoryTheory.CatCommSq

/-!
# Algebraic target naturality for the twice-spiral model

This file composes the three existing target-postcomposition comparisons from
connector vertex data through coordinate data and pushout representations to
single-object functors.  The component squares retain the comparison
isomorphisms proved in their focused construction files.
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.TwiceSpiralAlgebraicTargetNaturality

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralConnectorVertexExtraction
open ConstructionTargets.TwiceSpiralConnectorVertexMorphisms
open ConstructionTargets.TwiceSpiralCoordinateVertexEquivalence
open ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralPushoutRepresentations
open ConstructionTargets.TwiceSpiralPushoutRepresentationEquivalence
open ConstructionTargets.TwiceSpiralPushoutRepresentationRoundTrip
open ConstructionTargets.TwiceSpiralPushoutSingleObjEquivalence
open ConstructionTargets.TwiceSpiralPushoutTargetNaturality
open ConstructionTargets.TwiceSpiralRepresentabilityCandidates
open ConstructionTargets.TwiceSpiralVertexTargetNaturality

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d) (K : LegCompatibleConnectorSystems B)
variable {C D : Type} [Groupoid C] [Groupoid D]

/-- The left-associated algebraic equivalence from connector vertex data to
functors out of the single-object twice-spiral pushout. -/
def vertexToSingleObjEquivalence (C : Type) [Groupoid C] :
    VertexData B C K ≌ (SingleObj (TwiceSpiralPushout d) ⥤ C) :=
  ((vertexDataCoordinateEquivalence B C K).trans
    (coordinatePushoutRepresentationEquivalence (d := d) C)).trans
      (pushoutRepresentationSingleObjEquivalence (d := d) C)

/-- Target postcomposition commutes with vertex-to-coordinate transport. -/
@[reducible] def vertexCoordinateSquare (H : C ⥤ D) : CatCommSq
    (postcomposeVertexDataFunctor B K H)
    (vertexDataCoordinateEquivalence B C K).functor
    (vertexDataCoordinateEquivalence B D K).functor
    (postcomposeCoordinateVertexFunctor (d := d) H) where
  iso := toCoordinatePostcomposeIso B K H

/-- Target postcomposition commutes with coordinate-to-pushout transport. -/
@[reducible] def coordinatePushoutSquare (H : C ⥤ D) : CatCommSq
    (postcomposeCoordinateVertexFunctor (d := d) H)
    (coordinatePushoutRepresentationEquivalence (d := d) C).functor
    (coordinatePushoutRepresentationEquivalence (d := d) D).functor
    (postcomposeRepresentationFunctor (d := d) H) where
  iso := coordinateToPushoutPostcomposeIso (d := d) H

/-- Target postcomposition commutes with the representation-to-single-object
functor equivalence. -/
@[reducible] def representationSingleObjSquare (H : C ⥤ D) : CatCommSq
    (postcomposeRepresentationFunctor (d := d) H)
    (pushoutRepresentationSingleObjEquivalence (d := d) C).functor
    (pushoutRepresentationSingleObjEquivalence (d := d) D).functor
    ((Functor.whiskeringRight
      (SingleObj (TwiceSpiralPushout d)) C D).obj H) where
  iso := representationToFunctorPostcomposeIso (d := d) H

/-- The inverse mate of the coordinate-to-pushout square. -/
@[reducible] def pushoutCoordinateMate (H : C ⥤ D) : CatCommSq
    (postcomposeRepresentationFunctor (d := d) H)
    (coordinatePushoutRepresentationEquivalence (d := d) C).inverse
    (coordinatePushoutRepresentationEquivalence (d := d) D).inverse
    (postcomposeCoordinateVertexFunctor (d := d) H) :=
  CatCommSq.vInv
    (postcomposeCoordinateVertexFunctor (d := d) H)
    (coordinatePushoutRepresentationEquivalence (d := d) C)
    (coordinatePushoutRepresentationEquivalence (d := d) D)
    (postcomposeRepresentationFunctor (d := d) H)
    (coordinatePushoutSquare (d := d) H)

/-- The inverse mate of the representation-to-single-object square. -/
@[reducible] def singleObjRepresentationMate (H : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight
      (SingleObj (TwiceSpiralPushout d)) C D).obj H)
    (pushoutRepresentationSingleObjEquivalence (d := d) C).inverse
    (pushoutRepresentationSingleObjEquivalence (d := d) D).inverse
    (postcomposeRepresentationFunctor (d := d) H) :=
  CatCommSq.vInv
    (postcomposeRepresentationFunctor (d := d) H)
    (pushoutRepresentationSingleObjEquivalence (d := d) C)
    (pushoutRepresentationSingleObjEquivalence (d := d) D)
    ((Functor.whiskeringRight
      (SingleObj (TwiceSpiralPushout d)) C D).obj H)
    (representationSingleObjSquare (d := d) H)

/-- The first two algebraic target-naturality squares, vertically composed. -/
@[reducible] def vertexPushoutSquare (H : C ⥤ D) :=
  CatCommSq.vComp'
    (vertexCoordinateSquare B K H)
    (coordinatePushoutSquare (d := d) H)

/-- The complete forward target-naturality square from raw vertex data to
single-object functors. -/
@[reducible] def vertexSingleObjSquare (H : C ⥤ D) : CatCommSq
    (postcomposeVertexDataFunctor B K H)
    (vertexToSingleObjEquivalence B K C).functor
    (vertexToSingleObjEquivalence B K D).functor
    ((Functor.whiskeringRight
      (SingleObj (TwiceSpiralPushout d)) C D).obj H) :=
  CatCommSq.vComp'
    (vertexPushoutSquare B K H)
    (representationSingleObjSquare (d := d) H)

/-- The inverse mate of the complete algebraic target-naturality square:
postcomposition on single-object functors followed by inverse transport agrees
with inverse transport followed by postcomposition on vertex data. -/
@[reducible] def singleObjVertexMate (H : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight
      (SingleObj (TwiceSpiralPushout d)) C D).obj H)
    (vertexToSingleObjEquivalence B K C).inverse
    (vertexToSingleObjEquivalence B K D).inverse
    (postcomposeVertexDataFunctor B K H) :=
  CatCommSq.vInv
    (postcomposeVertexDataFunctor B K H)
    (vertexToSingleObjEquivalence B K C)
    (vertexToSingleObjEquivalence B K D)
    ((Functor.whiskeringRight
      (SingleObj (TwiceSpiralPushout d)) C D).obj H)
    (vertexSingleObjSquare B K H)

#print axioms vertexToSingleObjEquivalence
#print axioms pushoutCoordinateMate
#print axioms singleObjRepresentationMate
#print axioms vertexSingleObjSquare
#print axioms singleObjVertexMate

end ConstructionTargets.TwiceSpiralAlgebraicTargetNaturality
