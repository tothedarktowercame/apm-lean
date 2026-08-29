import ConstructionTargets.TwiceSpiralRepresentabilityCandidates
import Mathlib.CategoryTheory.Conj

open CategoryTheory
noncomputable section

namespace ConstructionTargets.TwiceSpiralPushoutTargetNaturality

open ConstructionTargets.TwiceSpiralCoordinateVertexRepresentations
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralPushoutRepresentations
open ConstructionTargets.TwiceSpiralPushoutRepresentationEquivalence
open ConstructionTargets.TwiceSpiralRepresentabilityCandidates

variable {d : ℤ} {C D : Type} [Groupoid C] [Groupoid D]

def postcomposeCoordinateVertexObj (H : C ⥤ D)
    (R : CoordinateVertexData (d := d) C) : CoordinateVertexData (d := d) D where
  leftTarget := H.obj R.leftTarget
  rightTarget := H.obj R.rightTarget
  baseGlue := H.mapIso R.baseGlue
  leftHom := {
    toFun := fun g => H.map (R.leftHom g)
    map_one' := by
      rw [R.leftHom.map_one]
      exact H.map_id _
    map_mul' := by
      intro x y
      rw [R.leftHom.map_mul]
      exact H.map_comp _ _ }
  rightHom := {
    toFun := fun g => H.map (R.rightHom g)
    map_one' := by
      rw [R.rightHom.map_one]
      exact H.map_id _
    map_mul' := by
      intro x y
      rw [R.rightHom.map_mul]
      exact H.map_comp _ _ }
  boundaryCompatibility := by
    ext x
    have hx := DFunLike.congr_fun R.boundaryCompatibility x
    exact (H.map_conj R.baseGlue (R.leftHom (leftBoundaryHom x))).symm.trans
      (congrArg H.map hx)

def postcomposeCoordinateVertexMap (H : C ⥤ D)
    {R S : CoordinateVertexData (d := d) C} (f : R ⟶ S) :
    postcomposeCoordinateVertexObj H R ⟶ postcomposeCoordinateVertexObj H S where
  left := H.map f.left
  right := H.map f.right
  left_intertwines g := by
    change H.map (R.leftHom g) ≫ H.map f.left =
      H.map f.left ≫ H.map (S.leftHom g)
    rw [← H.map_comp, ← H.map_comp, f.left_intertwines]
  right_intertwines g := by
    change H.map (R.rightHom g) ≫ H.map f.right =
      H.map f.right ≫ H.map (S.rightHom g)
    rw [← H.map_comp, ← H.map_comp, f.right_intertwines]
  baseGlue_square := by
    change H.map R.baseGlue.hom ≫ H.map f.right =
      H.map f.left ≫ H.map S.baseGlue.hom
    rw [← H.map_comp, ← H.map_comp, f.baseGlue_square]

def postcomposeCoordinateVertexFunctor (H : C ⥤ D) :
    CoordinateVertexData (d := d) C ⥤ CoordinateVertexData (d := d) D where
  obj := postcomposeCoordinateVertexObj H
  map := postcomposeCoordinateVertexMap H
  map_id R := by
    apply CoordinateVertexDataHom.ext <;> exact H.map_id _
  map_comp f g := by
    apply CoordinateVertexDataHom.ext <;> exact H.map_comp _ _

/-- Mapping the strictly glued pushout action agrees with first mapping the
coordinate datum and then rebuilding its strict action. -/
theorem postcompose_coordinate_pushout_action (H : C ⥤ D)
    (R : CoordinateVertexData (d := d) C) :
    (coordinateToPushoutObj D (postcomposeCoordinateVertexObj H R)).action =
      (postcomposeRepresentationObj H (coordinateToPushoutObj C R)).action := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro b
  apply DFunLike.ext
  intro g
  cases b
  · change H.map (R.leftHom g) = H.map (R.leftHom g)
    rfl
  · change (H.mapIso R.baseGlue).symm.conj (H.map (R.rightHom g)) =
      H.map (R.baseGlue.symm.conj (R.rightHom g))
    simpa using (H.map_conj R.baseGlue.symm (R.rightHom g)).symm

/-- Target postcomposition commutes with coordinate-to-pushout conversion. -/
def coordinateToPushoutPostcomposeIso (H : C ⥤ D) :
    postcomposeCoordinateVertexFunctor (d := d) H ⋙
        coordinateToPushoutFunctor D ≅
      coordinateToPushoutFunctor C ⋙ postcomposeRepresentationFunctor H :=
  NatIso.ofComponents (fun R => {
    hom := ⟨𝟙 _, by
      intro g
      change (coordinateToPushoutObj D
          (postcomposeCoordinateVertexObj H R)).action g ≫ 𝟙 _ =
        𝟙 _ ≫ (postcomposeRepresentationObj H
          (coordinateToPushoutObj C R)).action g
      rw [postcompose_coordinate_pushout_action H R]
      simp
      rfl⟩
    inv := ⟨𝟙 _, by
      intro g
      change (postcomposeRepresentationObj H
          (coordinateToPushoutObj C R)).action g ≫ 𝟙 _ =
        𝟙 _ ≫ (coordinateToPushoutObj D
          (postcomposeCoordinateVertexObj H R)).action g
      rw [postcompose_coordinate_pushout_action H R]
      simp
      rfl⟩
    hom_inv_id := by
      apply PushoutRepresentationHom.ext
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp
    inv_hom_id := by
      apply PushoutRepresentationHom.ext
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      simp }) (by
      intro R S f
      apply PushoutRepresentationHom.ext
      change H.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ H.map f.left
      simp)

@[simp] theorem coordinateToPushoutPostcomposeIso_hom
    (H : C ⥤ D) (R : CoordinateVertexData (d := d) C) :
    ((coordinateToPushoutPostcomposeIso (d := d) H).hom.app R).hom = 𝟙 _ := rfl

#print axioms postcomposeCoordinateVertexFunctor
#print axioms postcompose_coordinate_pushout_action
#print axioms coordinateToPushoutPostcomposeIso

end ConstructionTargets.TwiceSpiralPushoutTargetNaturality
