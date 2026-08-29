import ConstructionTargets.TwiceSpiralPushoutRepresentationEquivalence

/-!
# Round trips for twice-spiral pushout representations

The two generator formulas for `Monoid.PushoutI.lift` identify the recovered
pushout action with the original action.  On coordinate data, the round-trip
comparison is identity on the left target and the original `baseGlue` on the
right target.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralPushoutRepresentationRoundTrip

open ConstructionTargets.TwiceSpiralCoordinateVertexEquivalence
open ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralPushoutRepresentationEquivalence
open ConstructionTargets.TwiceSpiralPushoutRepresentations

variable {d : ℤ} (C : Type) [Groupoid C]

/-- Restricting an action to the two legs and lifting it again recovers the
original action. -/
theorem recoveredPushoutAction_eq (R : PushoutRepresentation (d := d) C) :
    (coordinateToPushoutObj C (pushoutToCoordinateObj C R)).action = R.action := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro b
  apply DFunLike.ext
  intro g
  cases b
  · change (coordinateToPushoutObj C (pushoutToCoordinateObj C R)).action
        (Monoid.PushoutI.of false g) = R.action (Monoid.PushoutI.of false g)
    simpa [pushoutToCoordinateObj] using
      (coordinateToPushoutObj_action_of_false C (pushoutToCoordinateObj C R) g)
  · change (coordinateToPushoutObj C (pushoutToCoordinateObj C R)).action
        (Monoid.PushoutI.of true g) = R.action (Monoid.PushoutI.of true g)
    rw [coordinateToPushoutObj_action_of_true]
    change (Iso.refl R.target).symm.conj
      (R.action (Monoid.PushoutI.of true g)) = R.action (Monoid.PushoutI.of true g)
    simp [Iso.conj_apply]

/-- The pushout-side round trip uses the identity target arrow. -/
def pushoutRoundTripIso (R : PushoutRepresentation (d := d) C) :
    ((pushoutToCoordinateFunctor C) ⋙ (coordinateToPushoutFunctor C)).obj R ≅ R where
  hom := {
    hom := 𝟙 _
    intertwines := by
      intro g
      change (coordinateToPushoutObj C (pushoutToCoordinateObj C R)).action g ≫ 𝟙 _ =
        𝟙 _ ≫ R.action g
      rw [recoveredPushoutAction_eq C R]
      simp only [Category.comp_id, Category.id_comp]
      rfl }
  inv := {
    hom := 𝟙 _
    intertwines := by
      intro g
      change R.action g ≫ 𝟙 _ = 𝟙 _ ≫
        (coordinateToPushoutObj C (pushoutToCoordinateObj C R)).action g
      rw [recoveredPushoutAction_eq C R]
      simp only [Category.comp_id, Category.id_comp]
      rfl }
  hom_inv_id := by
    apply PushoutRepresentationHom.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply PushoutRepresentationHom.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- Coordinate-side comparison from the strictified/restricted datum to the
original datum. -/
def coordinateRoundTripHom (D : CoordinateVertexData (d := d) C) :
    ((coordinateToPushoutFunctor C) ⋙ (pushoutToCoordinateFunctor C)).obj D ⟶ D where
  left := 𝟙 _
  right := D.baseGlue.hom
  left_intertwines := by
    intro g
    change (coordinateToPushoutObj C D).action (Monoid.PushoutI.of false g) ≫ 𝟙 _ =
      𝟙 _ ≫ D.leftHom g
    rw [coordinateToPushoutObj_action_of_false]
    simp
  right_intertwines := by
    intro g
    change strictRightHom C D g ≫ D.baseGlue.hom =
      D.baseGlue.hom ≫ D.rightHom g
    simp [strictRightHom, Iso.conj_apply]
  baseGlue_square := by
    change (𝟙 D.leftTarget) ≫ D.baseGlue.hom = 𝟙 _ ≫ D.baseGlue.hom
    simp

/-- Inverse coordinate-side comparison. -/
def coordinateRoundTripInv (D : CoordinateVertexData (d := d) C) :
    D ⟶ ((coordinateToPushoutFunctor C) ⋙ (pushoutToCoordinateFunctor C)).obj D where
  left := 𝟙 _
  right := D.baseGlue.inv
  left_intertwines := by
    intro g
    change D.leftHom g ≫ 𝟙 _ = 𝟙 _ ≫
      (coordinateToPushoutObj C D).action (Monoid.PushoutI.of false g)
    rw [coordinateToPushoutObj_action_of_false]
    simp
  right_intertwines := by
    intro g
    change D.rightHom g ≫ D.baseGlue.inv =
      D.baseGlue.inv ≫ strictRightHom C D g
    simp [strictRightHom, Iso.conj_apply]
  baseGlue_square := by
    change D.baseGlue.hom ≫ D.baseGlue.inv = 𝟙 _ ≫ 𝟙 _
    simp

def coordinatePushoutRoundTripIso (D : CoordinateVertexData (d := d) C) :
    ((coordinateToPushoutFunctor C) ⋙ (pushoutToCoordinateFunctor C)).obj D ≅ D where
  hom := coordinateRoundTripHom C D
  inv := coordinateRoundTripInv C D
  hom_inv_id := by
    apply CoordinateVertexDataHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
    · change D.baseGlue.hom ≫ D.baseGlue.inv = 𝟙 _; simp
  inv_hom_id := by
    apply CoordinateVertexDataHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
    · change D.baseGlue.inv ≫ D.baseGlue.hom = 𝟙 _; simp

theorem coordinatePushoutRoundTripIso_naturality
    {D E : CoordinateVertexData (d := d) C} (f : D ⟶ E) :
    ((coordinateToPushoutFunctor C) ⋙ (pushoutToCoordinateFunctor C)).map f ≫
        (coordinatePushoutRoundTripIso C E).hom =
      (coordinatePushoutRoundTripIso C D).hom ≫ f := by
  apply CoordinateVertexDataHom.ext
  · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
  · exact f.baseGlue_square.symm

theorem pushoutRoundTripIso_naturality
    {D E : PushoutRepresentation (d := d) C} (f : D ⟶ E) :
    ((pushoutToCoordinateFunctor C) ⋙ (coordinateToPushoutFunctor C)).map f ≫
        (pushoutRoundTripIso C E).hom =
      (pushoutRoundTripIso C D).hom ≫ f := by
  apply PushoutRepresentationHom.ext
  change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
  simp

def coordinatePushoutRoundTripNatIso :
    (coordinateToPushoutFunctor C) ⋙ (pushoutToCoordinateFunctor C) ≅
      𝟭 (CoordinateVertexData (d := d) C) :=
  NatIso.ofComponents (coordinatePushoutRoundTripIso C) (by
    intro D E f
    exact coordinatePushoutRoundTripIso_naturality C f)

def pushoutRoundTripNatIso :
    (pushoutToCoordinateFunctor C) ⋙ (coordinateToPushoutFunctor C) ≅
      𝟭 (PushoutRepresentation (d := d) C) :=
  NatIso.ofComponents (pushoutRoundTripIso C) (by
    intro D E f
    exact pushoutRoundTripIso_naturality C f)

theorem coordinatePushout_triangle (D : CoordinateVertexData (d := d) C) :
    (coordinateToPushoutFunctor C).map
          ((coordinatePushoutRoundTripNatIso C).symm.hom.app D) ≫
        (pushoutRoundTripNatIso C).hom.app
          ((coordinateToPushoutFunctor C).obj D) =
      𝟙 ((coordinateToPushoutFunctor C).obj D) := by
  apply PushoutRepresentationHom.ext
  change (𝟙 D.leftTarget) ≫ 𝟙 D.leftTarget = 𝟙 D.leftTarget
  simp

/-- Equivalence between integer-coordinate vertex data and representations of
the actual twice-spiral pushout. -/
def coordinatePushoutRepresentationEquivalence :
    CoordinateVertexData (d := d) C ≌ PushoutRepresentation (d := d) C :=
  CategoryTheory.Equivalence.mk'
    (coordinateToPushoutFunctor C)
    (pushoutToCoordinateFunctor C)
    (coordinatePushoutRoundTripNatIso C).symm
    (pushoutRoundTripNatIso C)
    (coordinatePushout_triangle C)

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus}

/-- Mapping-category description of the gluing groupoid by representations of
the literal twice-spiral pushout. -/
def gluingFundamentalGroupoidPushoutRepresentationEquivalence
    (B : PointedCoordinateBases h d) (K : LegCompatibleConnectorSystems B) :
    Functor (FundamentalGroupoid (Gluing h)) C ≌ PushoutRepresentation (d := d) C :=
  (gluingFundamentalGroupoidCoordinateVertexEquivalence B C K).trans
    (coordinatePushoutRepresentationEquivalence C)

#print axioms recoveredPushoutAction_eq
#print axioms coordinatePushoutRoundTripIso
#print axioms pushoutRoundTripIso
#print axioms coordinatePushoutRepresentationEquivalence
#print axioms gluingFundamentalGroupoidPushoutRepresentationEquivalence

end ConstructionTargets.TwiceSpiralPushoutRepresentationRoundTrip
