import ConstructionTargets.TwiceSpiralCoordinateVertexEquivalence

/-!
# Representations of the twice-spiral pushout

This file passes from the two integer actions in `CoordinateVertexData` to an
action of the actual monoid pushout.  The right action is first transported to
the left target through the inverse of `baseGlue`; the pushout action is then
constructed with `Monoid.PushoutI.lift`.
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.TwiceSpiralPushoutRepresentations

open ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout

variable {d : ℤ} (C : Type) [Groupoid C]

/-- A representation of the literal twice-spiral monoid pushout in a groupoid. -/
structure PushoutRepresentation where
  target : C
  action : TwiceSpiralPushout d →* End target

/-- Intertwiners of pushout representations. -/
structure PushoutRepresentationHom
    (D E : PushoutRepresentation (d := d) C) where
  hom : D.target ⟶ E.target
  intertwines : ∀ g, D.action g ≫ hom = hom ≫ E.action g

@[ext] theorem PushoutRepresentationHom.ext
    {D E : PushoutRepresentation (d := d) C}
    {f g : PushoutRepresentationHom C D E} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp_all

instance : Category (PushoutRepresentation (d := d) C) where
  Hom := PushoutRepresentationHom C
  id D := ⟨𝟙 _, by intro; simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    intro x
    rw [← Category.assoc, f.intertwines, Category.assoc,
      g.intertwines, ← Category.assoc]⟩
  id_comp _ := by ext; simp
  comp_id _ := by ext; simp
  assoc _ _ _ := by ext; simp [Category.assoc]

/-- The coordinate right action transported onto the left target. -/
def strictRightHom (D : CoordinateVertexData (d := d) C) :
    IntGroup →* End D.leftTarget :=
  D.baseGlue.symm.conj.toMonoidHom.comp D.rightHom

/-- After transport to the left target, the two actions agree on the literal
boundary maps. -/
theorem strict_actions_compatible (D : CoordinateVertexData (d := d) C) :
    D.leftHom.comp leftBoundaryHom =
      (strictRightHom C D).comp (rightBoundaryHom d) := by
  ext x
  have h := DFunLike.congr_fun D.boundaryCompatibility x
  change D.baseGlue.conj (D.leftHom (leftBoundaryHom x)) =
    D.rightHom (rightBoundaryHom d x) at h
  change D.leftHom (leftBoundaryHom x) =
    D.baseGlue.symm.conj (D.rightHom (rightBoundaryHom d x))
  rw [← h]
  simp

/-- The compatible Bool-indexed family supplied to `PushoutI.lift`. -/
def strictActionFamily (D : CoordinateVertexData (d := d) C) :
    ∀ b : Bool, IntGroup →* End D.leftTarget
  | false => D.leftHom
  | true => strictRightHom C D

theorem strictActionFamily_compatible (D : CoordinateVertexData (d := d) C) :
    ∀ b, (strictActionFamily C D b).comp (twiceSpiralDiagram d b) =
      D.leftHom.comp leftBoundaryHom := by
  intro b
  cases b
  · rfl
  · exact (strict_actions_compatible C D).symm

/-- Strictify a coordinate datum onto its left target and apply the genuine
`PushoutI.lift` universal property. -/
def coordinateToPushoutObj (D : CoordinateVertexData (d := d) C) :
    PushoutRepresentation (d := d) C where
  target := D.leftTarget
  action := Monoid.PushoutI.lift (strictActionFamily C D)
    (D.leftHom.comp leftBoundaryHom) (strictActionFamily_compatible C D)

@[simp] theorem coordinateToPushoutObj_action_of_false
    (D : CoordinateVertexData (d := d) C) (g : IntGroup) :
    (coordinateToPushoutObj C D).action
        (Monoid.PushoutI.of false g) = D.leftHom g := by
  exact Monoid.PushoutI.lift_of (strictActionFamily C D)
    (D.leftHom.comp leftBoundaryHom) (strictActionFamily_compatible C D)
    (i := false) g

@[simp] theorem coordinateToPushoutObj_action_of_true
    (D : CoordinateVertexData (d := d) C) (g : IntGroup) :
    (coordinateToPushoutObj C D).action
        (Monoid.PushoutI.of true g) = strictRightHom C D g := by
  exact Monoid.PushoutI.lift_of (strictActionFamily C D)
    (D.leftHom.comp leftBoundaryHom) (strictActionFamily_compatible C D)
    (i := true) g

/-- Restrict a pushout action along its two canonical legs.  The two target
objects are literally equal and the glue is the identity. -/
def pushoutToCoordinateObj (R : PushoutRepresentation (d := d) C) :
    CoordinateVertexData (d := d) C where
  leftTarget := R.target
  rightTarget := R.target
  baseGlue := Iso.refl _
  leftHom := R.action.comp
    (Monoid.PushoutI.of (φ := twiceSpiralDiagram d) false)
  rightHom := R.action.comp
    (Monoid.PushoutI.of (φ := twiceSpiralDiagram d) true)
  boundaryCompatibility := by
    apply DFunLike.ext
    intro x
    change (Iso.refl R.target).conj
        (R.action (Monoid.PushoutI.of false (twiceSpiralDiagram d false x))) =
      R.action (Monoid.PushoutI.of true (twiceSpiralDiagram d true x))
    rw [Iso.refl_conj]
    rw [Monoid.PushoutI.of_apply_eq_base, Monoid.PushoutI.of_apply_eq_base]

theorem pushoutToCoordinateObj_leftHom
    (R : PushoutRepresentation (d := d) C) :
    (pushoutToCoordinateObj C R).leftHom =
      R.action.comp (Monoid.PushoutI.of (φ := twiceSpiralDiagram d) false) := rfl

theorem pushoutToCoordinateObj_rightHom
    (R : PushoutRepresentation (d := d) C) :
    (pushoutToCoordinateObj C R).rightHom =
      R.action.comp (Monoid.PushoutI.of (φ := twiceSpiralDiagram d) true) := rfl

#print axioms strict_actions_compatible
#print axioms coordinateToPushoutObj
#print axioms coordinateToPushoutObj_action_of_false
#print axioms coordinateToPushoutObj_action_of_true
#print axioms pushoutToCoordinateObj

end ConstructionTargets.TwiceSpiralPushoutRepresentations
