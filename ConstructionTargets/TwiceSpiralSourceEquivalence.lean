import ConstructionTargets.TwiceSpiralFinalTargetNaturality
import ConstructionTargets.TwiceSpiralRepresentabilityCandidates

/-!
# Source equivalence for the twice-spiral gluing groupoid

This file reconstructs an equivalence of the two source groupoids from the
consumer-facing mapping-category equivalences.  It uses the already proved
pointwise target-postcomposition squares at the two candidate functors, then
reflects the resulting isomorphisms through fully faithful functors.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralSourceEquivalence

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralFinalTargetNaturality
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralPushoutSingleObjEquivalence
open ConstructionTargets.TwiceSpiralRepresentabilityCandidates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d) (K : LegCompatibleConnectorSystems B)

abbrev gluingGroupoid := FundamentalGroupoid (Gluing h)
abbrev pushoutSingleObj := SingleObj (TwiceSpiralPushout d)

abbrev mappingEquivalence (C : Type) [Groupoid C] :=
  gluingFundamentalGroupoidSingleObjMappingEquivalence (C := C) B K

abbrev gluingToPushout :
    Functor (gluingGroupoid (h := h)) (pushoutSingleObj (d := d)) :=
  gluingToPushoutCandidate B K

abbrev pushoutToGluing :
    Functor (pushoutSingleObj (d := d)) (gluingGroupoid (h := h)) :=
  pushoutToGluingCandidate B K

/-- The image of `gluingToPushout ⋙ pushoutToGluing` is isomorphic to the
image of the identity.  The first factor is target naturality evaluated at
`gluingToPushout`; the remaining factors use the mapping equivalence's
counit and the left unitor. -/
def gluingRoundTripImageIso :
    (mappingEquivalence B K (gluingGroupoid (h := h))).functor.obj
        (gluingToPushout B K ⋙ pushoutToGluing B K) ≅
      (mappingEquivalence B K (gluingGroupoid (h := h))).functor.obj
        (Functor.id (gluingGroupoid (h := h))) :=
  (gluingFundamentalGroupoidSingleObjMappingEquivalence_postcomposeIso
      B K (pushoutToGluing B K)).app (gluingToPushout B K) ≪≫
    Functor.isoWhiskerRight
      ((mappingEquivalence B K (pushoutSingleObj (d := d))).counitIso.app
        (Functor.id (pushoutSingleObj (d := d))))
      (pushoutToGluing B K) ≪≫
    Functor.leftUnitor (pushoutToGluing B K)

/-- Full faithfulness of the mapping-equivalence functor reflects the first
round-trip image isomorphism back to the gluing groupoid. -/
def gluingRoundTripIso :
    gluingToPushout B K ⋙ pushoutToGluing B K ≅
      Functor.id (gluingGroupoid (h := h)) :=
  (mappingEquivalence B K (gluingGroupoid (h := h))).functor.preimageIso
    (gluingRoundTripImageIso B K)

/-- The inverse mapping-equivalence mate, evaluated at `pushoutToGluing`,
identifies the image of the other composite with the image of the identity.
The unit of the mapping equivalence supplies the middle comparison. -/
def pushoutRoundTripImageIso :
    (mappingEquivalence B K (pushoutSingleObj (d := d))).inverse.obj
        (pushoutToGluing B K ⋙ gluingToPushout B K) ≅
      (mappingEquivalence B K (pushoutSingleObj (d := d))).inverse.obj
        (Functor.id (pushoutSingleObj (d := d))) :=
  (gluingFundamentalGroupoidSingleObjMappingEquivalence_inversePostcomposeIso
      B K (gluingToPushout B K)).app (pushoutToGluing B K) ≪≫
    Functor.isoWhiskerRight
      ((mappingEquivalence B K (gluingGroupoid (h := h))).unitIso.app
        (Functor.id (gluingGroupoid (h := h)))).symm
      (gluingToPushout B K) ≪≫
    Functor.leftUnitor (gluingToPushout B K)

/-- Full faithfulness of the inverse mapping-equivalence functor reflects the
second round-trip image isomorphism back to the one-object pushout category. -/
def pushoutRoundTripIso :
    pushoutToGluing B K ⋙ gluingToPushout B K ≅
      Functor.id (pushoutSingleObj (d := d)) :=
  (mappingEquivalence B K (pushoutSingleObj (d := d))).inverse.preimageIso
    (pushoutRoundTripImageIso B K)

/-- The fundamental groupoid of the twice-spiral gluing is equivalent to the
one-object category of its algebraic pushout.  `Equivalence.mk` adjointifies
the two reflected round-trip isomorphisms and supplies the triangle law. -/
def gluingFundamentalGroupoidSingleObjEquivalence :
    FundamentalGroupoid (Gluing h) ≌ SingleObj (TwiceSpiralPushout d) :=
  CategoryTheory.Equivalence.mk
    (gluingToPushout B K) (pushoutToGluing B K)
    (gluingRoundTripIso B K).symm (pushoutRoundTripIso B K)

#print axioms gluingRoundTripImageIso
#print axioms gluingRoundTripIso
#print axioms pushoutRoundTripImageIso
#print axioms pushoutRoundTripIso
#print axioms gluingFundamentalGroupoidSingleObjEquivalence

end ConstructionTargets.TwiceSpiralSourceEquivalence
