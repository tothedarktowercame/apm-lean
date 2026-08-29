import ConstructionTargets.TwiceSpiralPushoutRepresentations

open CategoryTheory
noncomputable section

namespace ConstructionTargets.TwiceSpiralPushoutRepresentationEquivalence

open ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralPushoutRepresentations

variable {d : ℤ} (C : Type) [Groupoid C]

theorem intertwines_iff_conj {A B : C} (e : A ≅ B) (a : End A) (b : End B) :
    a ≫ e.hom = e.hom ≫ b ↔ e.conj a = b := by
  constructor
  · intro h
    rw [Iso.conj_apply, h]
    simp
  · intro h
    rw [Iso.conj_apply] at h
    rw [← cancel_epi e.inv]
    simpa [Category.assoc] using h

theorem strictRight_intertwines {D E : CoordinateVertexData (d := d) C}
    (f : D ⟶ E) (g : IntGroup) :
    strictRightHom C D g ≫ f.left = f.left ≫ strictRightHom C E g := by
  have hi : D.baseGlue.inv ≫ f.left = f.right ≫ E.baseGlue.inv := by
    rw [← cancel_epi D.baseGlue.hom]
    simp only [D.baseGlue.hom_inv_id_assoc]
    calc
      f.left = f.left ≫ (E.baseGlue.hom ≫ E.baseGlue.inv) := by simp
      _ = (f.left ≫ E.baseGlue.hom) ≫ E.baseGlue.inv := by
        simp [Category.assoc]
      _ = (D.baseGlue.hom ≫ f.right) ≫ E.baseGlue.inv := by
        rw [f.baseGlue_square]
      _ = D.baseGlue.hom ≫ f.right ≫ E.baseGlue.inv := by
        simp [Category.assoc]
  rw [strictRightHom, strictRightHom]
  change (D.baseGlue.hom ≫ D.rightHom g ≫ D.baseGlue.inv) ≫ f.left =
    f.left ≫ E.baseGlue.hom ≫ E.rightHom g ≫ E.baseGlue.inv
  calc
    _ = D.baseGlue.hom ≫ D.rightHom g ≫
        (D.baseGlue.inv ≫ f.left) := by simp [Category.assoc]
    _ = D.baseGlue.hom ≫ D.rightHom g ≫
        (f.right ≫ E.baseGlue.inv) := by rw [hi]
    _ = D.baseGlue.hom ≫ (D.rightHom g ≫ f.right) ≫
        E.baseGlue.inv := by simp [Category.assoc]
    _ = D.baseGlue.hom ≫ (f.right ≫ E.rightHom g) ≫
        E.baseGlue.inv := by rw [f.right_intertwines]
    _ = (D.baseGlue.hom ≫ f.right) ≫ E.rightHom g ≫
        E.baseGlue.inv := by simp [Category.assoc]
    _ = (f.left ≫ E.baseGlue.hom) ≫ E.rightHom g ≫
        E.baseGlue.inv := by rw [f.baseGlue_square]
    _ = _ := by simp [Category.assoc]

def coordinateToPushoutMap {D E : CoordinateVertexData (d := d) C} (f : D ⟶ E) :
    coordinateToPushoutObj C D ⟶ coordinateToPushoutObj C E where
  hom := f.left
  intertwines g := by
    let e : D.leftTarget ≅ E.leftTarget := asIso f.left
    have hl : ∀ x : IntGroup, e.conj (D.leftHom x) = E.leftHom x :=
      fun x => (intertwines_iff_conj C e _ _).mp (f.left_intertwines x)
    have hr : ∀ x : IntGroup,
        e.conj (strictRightHom C D x) = strictRightHom C E x :=
      fun x => (intertwines_iff_conj C e _ _).mp (strictRight_intertwines C f x)
    have ha : e.conj.toMonoidHom.comp (coordinateToPushoutObj C D).action =
        (coordinateToPushoutObj C E).action := by
      apply Monoid.PushoutI.hom_ext_nonempty
      intro b
      apply DFunLike.ext
      intro x
      cases b
      · simpa using hl x
      · simpa using hr x
    exact (intertwines_iff_conj C e _ _).mpr (DFunLike.congr_fun ha g)

def pushoutToCoordinateMap {D E : PushoutRepresentation (d := d) C} (f : D ⟶ E) :
    pushoutToCoordinateObj C D ⟶ pushoutToCoordinateObj C E where
  left := f.hom
  right := f.hom
  left_intertwines g := f.intertwines (Monoid.PushoutI.of false g)
  right_intertwines g := f.intertwines (Monoid.PushoutI.of true g)
  baseGlue_square := by
    simp [pushoutToCoordinateObj]

def coordinateToPushoutFunctor :
    CoordinateVertexData (d := d) C ⥤ PushoutRepresentation (d := d) C where
  obj := coordinateToPushoutObj C
  map := coordinateToPushoutMap C
  map_id _ := by apply PushoutRepresentationHom.ext; rfl
  map_comp _ _ := by apply PushoutRepresentationHom.ext; rfl

def pushoutToCoordinateFunctor :
    PushoutRepresentation (d := d) C ⥤ CoordinateVertexData (d := d) C where
  obj := pushoutToCoordinateObj C
  map := pushoutToCoordinateMap C
  map_id _ := by apply CoordinateVertexDataHom.ext <;> rfl
  map_comp _ _ := by apply CoordinateVertexDataHom.ext <;> rfl

#print axioms coordinateToPushoutMap
#print axioms coordinateToPushoutFunctor
#print axioms pushoutToCoordinateFunctor

end ConstructionTargets.TwiceSpiralPushoutRepresentationEquivalence
