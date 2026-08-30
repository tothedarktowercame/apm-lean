import ConstructionTargets.TwiceSpiralAlgebraicTargetNaturality
import ConstructionTargets.TwiceSpiralPseudococoneTransport

/-!
# Final target naturality for the twice-spiral equivalence

This file pastes the geometric, pseudococone-coordinate, connector-extraction,
and algebraic target-postcomposition squares.  It obtains the reverse
comparison by taking the inverse mate of that composite square.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralFinalTargetNaturality

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates
open ConstructionTargets.TwiceSpiralFundamentalGroupoidOpenCover
open ConstructionTargets.TwiceSpiralPseudococoneTransport
open ConstructionTargets.TwiceSpiralConnectorVertexEquivalence
open ConstructionTargets.TwiceSpiralVertexTargetNaturality
open ConstructionTargets.TwiceSpiralAlgebraicTargetNaturality
open ConstructionTargets.TwiceSpiralPushoutSingleObjEquivalence
open ConstructionTargets.TwoOpenFundamentalGroupoidSpan

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d) (K : LegCompatibleConnectorSystems B)
variable {C D : Type} [Groupoid C] [Groupoid D]

/-- Target postcomposition commutes with the geometric pseudopushout
equivalence. -/
@[reducible] def gluingPseudopushoutPostcomposeSquare (H : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (FundamentalGroupoid (Gluing h)) C D).obj H)
    (gluingFundamentalGroupoidPseudopushoutEquivalence h C).functor
    (gluingFundamentalGroupoidPseudopushoutEquivalence h D).functor
    (postcomposePseudoFunctorCoconeFunctor H) where
  iso := gluingPseudopushoutPostcomposeNatIso h H

@[reducible] private def pastedTargetNaturalitySquare (H : C ⥤ D) :=
  CatCommSq.vComp'
    (CatCommSq.vComp'
      (CatCommSq.vComp'
        (gluingPseudopushoutPostcomposeSquare (h := h) H)
        (actualCoordinatePseudoCoconeEquivalence_targetNaturality
          (C := C) (D := D) h H))
      (extractionPostcomposeSquare B K H))
    (vertexSingleObjSquare B K H)

/-- The complete target-naturality square for the consumer-facing equivalence.
Its left-associated vertical composite reduces definitionally to
`gluingFundamentalGroupoidSingleObjMappingEquivalence`. -/
@[reducible] def
    gluingFundamentalGroupoidSingleObjMappingEquivalence_targetNaturalitySquare
    (H : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (FundamentalGroupoid (Gluing h)) C D).obj H)
    (gluingFundamentalGroupoidSingleObjMappingEquivalence (C := C) B K).functor
    (gluingFundamentalGroupoidSingleObjMappingEquivalence (C := D) B K).functor
    ((Functor.whiskeringRight (SingleObj (TwiceSpiralPushout d)) C D).obj H) :=
  pastedTargetNaturalitySquare B K H

/-- The forward natural isomorphism extracted from the complete square. -/
def gluingFundamentalGroupoidSingleObjMappingEquivalence_postcomposeIso
    (H : C ⥤ D) :
    (Functor.whiskeringRight
        (FundamentalGroupoid (Gluing h)) C D).obj H ⋙
      (gluingFundamentalGroupoidSingleObjMappingEquivalence
        (C := D) B K).functor
    ≅
    (gluingFundamentalGroupoidSingleObjMappingEquivalence
        (C := C) B K).functor ⋙
      (Functor.whiskeringRight
        (SingleObj (TwiceSpiralPushout d)) C D).obj H :=
  (gluingFundamentalGroupoidSingleObjMappingEquivalence_targetNaturalitySquare
    B K H).iso

/-- The inverse mate of the complete target-naturality square. -/
@[reducible] def
    gluingFundamentalGroupoidSingleObjMappingEquivalence_targetNaturalityMate
    (H : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (SingleObj (TwiceSpiralPushout d)) C D).obj H)
    (gluingFundamentalGroupoidSingleObjMappingEquivalence (C := C) B K).inverse
    (gluingFundamentalGroupoidSingleObjMappingEquivalence (C := D) B K).inverse
    ((Functor.whiskeringRight (FundamentalGroupoid (Gluing h)) C D).obj H) :=
  CatCommSq.vInv _ _ _ _
    (gluingFundamentalGroupoidSingleObjMappingEquivalence_targetNaturalitySquare
      B K H)

/-- The reverse-equivalence postcomposition comparison extracted from the
inverse mate. -/
def gluingFundamentalGroupoidSingleObjMappingEquivalence_inversePostcomposeIso
    (H : C ⥤ D) :
    (Functor.whiskeringRight
        (SingleObj (TwiceSpiralPushout d)) C D).obj H ⋙
      (gluingFundamentalGroupoidSingleObjMappingEquivalence
        (C := D) B K).inverse
    ≅
    (gluingFundamentalGroupoidSingleObjMappingEquivalence
        (C := C) B K).inverse ⋙
      (Functor.whiskeringRight
        (FundamentalGroupoid (Gluing h)) C D).obj H :=
  (gluingFundamentalGroupoidSingleObjMappingEquivalence_targetNaturalityMate
    B K H).iso

-- Definitional alignment check for the left-associated vertical composite.
example :
    ((gluingFundamentalGroupoidPseudopushoutEquivalence h C).trans
      ((actualCoordinatePseudoCoconeEquivalence h C).trans
        ((coordinatePseudoCoconeVertexDataEquivalence B C K).trans
          (vertexToSingleObjEquivalence B K C)))).functor =
      (gluingFundamentalGroupoidSingleObjMappingEquivalence
        (C := C) B K).functor := rfl

#print axioms gluingFundamentalGroupoidSingleObjMappingEquivalence_targetNaturalitySquare
#print axioms gluingFundamentalGroupoidSingleObjMappingEquivalence_postcomposeIso
#print axioms gluingFundamentalGroupoidSingleObjMappingEquivalence_targetNaturalityMate
#print axioms gluingFundamentalGroupoidSingleObjMappingEquivalence_inversePostcomposeIso

end ConstructionTargets.TwiceSpiralFinalTargetNaturality
