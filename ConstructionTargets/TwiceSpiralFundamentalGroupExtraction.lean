import ConstructionTargets.TwiceSpiralConnectorExistence
import ConstructionTargets.TwiceSpiralSourceEquivalence

/-!
# Chosen-object fundamental-group extraction for the twice spiral

This file selects the already proved nonempty compatible connector system and
extracts the endomorphism group at an arbitrary chosen point of the gluing.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralFundamentalGroupExtraction

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorExistence
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralSourceEquivalence

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}

/-- The connector data selected from the reviewed existence theorem. -/
def chosenLegCompatibleConnectorSystems (B : PointedCoordinateBases h d) :
    LegCompatibleConnectorSystems B :=
  Classical.choice (nonempty_legCompatibleConnectorSystems B)

/-- The source equivalence sends every chosen gluing object definitionally to
the unique object of the pushout's one-object category. -/
theorem gluingFundamentalGroupoidSingleObjEquivalence_obj
    (B : PointedCoordinateBases h d) (x : Gluing h) :
    (gluingFundamentalGroupoidSingleObjEquivalence B
      (chosenLegCompatibleConnectorSystems B)).functor.obj
        (FundamentalGroupoid.mk x) =
      SingleObj.star (TwiceSpiralPushout d) := rfl

/-- Extract the chosen-point fundamental group from the reviewed source
equivalence.  No connector premise remains in the public interface. -/
def gluingFundamentalGroupMulEquivPushout
    (B : PointedCoordinateBases h d) (x : Gluing h) :
    FundamentalGroup (Gluing h) x ≃* TwiceSpiralPushout d := by
  let K := chosenLegCompatibleConnectorSystems B
  let e := gluingFundamentalGroupoidSingleObjEquivalence B K
  exact (e.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk x)).trans
    (SingleObj.toEnd (TwiceSpiralPushout d)).symm

/-- Compose the extracted endomorphism group with the banked algebraic
identification of the twice-spiral pushout. -/
def gluingFundamentalGroupMulEquivZModTwo
    (B : PointedCoordinateBases h d) (x : Gluing h) :
    FundamentalGroup (Gluing h) x ≃* Multiplicative (ZMod 2) :=
  (gluingFundamentalGroupMulEquivPushout B x).trans
    (twiceSpiralPushoutMulEquivZModTwo d)

/-- Typed fixture recording the definitional chosen-object image used by the
endomorphism extraction. -/
example (B : PointedCoordinateBases h d) (x : Gluing h) :
    (gluingFundamentalGroupoidSingleObjEquivalence B
      (chosenLegCompatibleConnectorSystems B)).functor.obj
        (FundamentalGroupoid.mk x) =
      SingleObj.star (TwiceSpiralPushout d) := rfl

#print axioms gluingFundamentalGroupMulEquivPushout
#print axioms gluingFundamentalGroupMulEquivZModTwo

end ConstructionTargets.TwiceSpiralFundamentalGroupExtraction
