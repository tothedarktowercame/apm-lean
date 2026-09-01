import ConstructionTargets.GenericSpanPseudoCoconeTransport
import Mathlib.CategoryTheory.SingleObj
import Mathlib.GroupTheory.Coprod.Basic

open CategoryTheory
noncomputable section

namespace ConstructionTargets.FreeProductPointSpanRepresentations

open ConstructionTargets.GenericSpanPseudoCoconeTransport

variable {C : Type*} [Category C]

def pointHom (M : Type) [Monoid M] : PUnit.{1} →* M where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (mul_one 1).symm

def pointLeg (M : Type) [Monoid M] : SingleObj PUnit.{1} ⥤ SingleObj M :=
  (pointHom M).toFunctor

@[simp] theorem pointLeg_star_eq (M : Type) [Monoid M] :
    (pointLeg M).obj (SingleObj.star PUnit.{1}) = SingleObj.star M := by
  rfl

@[simp] theorem mapped_pointLeg_star_eq (M : Type) [Monoid M]
    (F : SingleObj M ⥤ C) :
    F.obj ((pointLeg M).obj (SingleObj.star PUnit.{1})) =
      F.obj (SingleObj.star M) := by
  rfl

def mappedPointLegStarIso (M : Type) [Monoid M] (F : SingleObj M ⥤ C) :
    F.obj ((pointLeg M).obj (SingleObj.star PUnit.{1})) ≅
      F.obj (SingleObj.star M) :=
  Iso.refl _

@[simp] theorem mappedPointLegStarIso_hom (M : Type) [Monoid M]
    (F : SingleObj M ⥤ C) :
    (mappedPointLegStarIso (C := C) M F).hom = 𝟙 _ := by
  rfl

@[simp] theorem mappedPointLegStarIso_inv (M : Type) [Monoid M]
    (F : SingleObj M ⥤ C) :
    (mappedPointLegStarIso (C := C) M F).inv = 𝟙 _ := by
  rfl

abbrev PointSpanPseudoCocone (G H : Type) [Monoid G] [Monoid H] :=
  SpanPseudoCocone (pointLeg G) (pointLeg H) C

def functorAction {M : Type} [Monoid M] (F : SingleObj M ⥤ C) :
    M →* End (F.obj (SingleObj.star M)) where
  toFun m := F.map m
  map_one' := F.map_id _
  map_mul' m n := by
    rw [End.mul_def, ← F.map_comp]
    exact congrArg F.map (SingleObj.comp_as_mul M n m).symm

structure PointSpanVertexData (G H : Type) [Monoid G] [Monoid H] where
  leftTarget : C
  rightTarget : C
  glue : leftTarget ≅ rightTarget
  leftAction : G →* End leftTarget
  rightAction : H →* End rightTarget

def vertexData (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) : PointSpanVertexData (C := C) G H where
  leftTarget := P.left.obj (SingleObj.star G)
  rightTarget := P.right.obj (SingleObj.star H)
  glue := P.glue.app (SingleObj.star PUnit)
  leftAction := functorAction (C := C) P.left
  rightAction := functorAction (C := C) P.right

def strictRightAction (G H : Type) [Monoid G] [Monoid H]
    (D : PointSpanVertexData (C := C) G H) : H →* End D.leftTarget :=
  { toFun := fun h => D.glue.hom ≫ D.rightAction h ≫ D.glue.inv
    map_one' := by simp
    map_mul' h₁ h₂ := by
      simp [D.rightAction.map_mul, Category.assoc] }

def freeProductAction (G H : Type) [Monoid G] [Monoid H]
    (D : PointSpanVertexData (C := C) G H) :
    Monoid.Coprod G H →* End D.leftTarget :=
  Monoid.Coprod.lift D.leftAction (strictRightAction (C := C) G H D)

@[simp] theorem freeProductAction_inl (G H : Type) [Monoid G] [Monoid H]
    (D : PointSpanVertexData (C := C) G H) (g : G) :
    freeProductAction (C := C) G H D (Monoid.Coprod.inl g) = D.leftAction g :=
  Monoid.Coprod.lift_apply_inl _ _ g

@[simp] theorem freeProductAction_inr (G H : Type) [Monoid G] [Monoid H]
    (D : PointSpanVertexData (C := C) G H) (h : H) :
    freeProductAction (C := C) G H D (Monoid.Coprod.inr h) =
      D.glue.hom ≫ D.rightAction h ≫ D.glue.inv := by
  rw [freeProductAction]
  rw [Monoid.Coprod.lift_apply_inr]
  rfl

structure FreeProductRepresentation (G H : Type) [Monoid G] [Monoid H] where
  target : C
  action : Monoid.Coprod G H →* End target

structure FreeProductRepresentationHom (G H : Type) [Monoid G] [Monoid H]
    (D E : FreeProductRepresentation (C := C) G H) where
  hom : D.target ⟶ E.target
  intertwines : ∀ x, D.action x ≫ hom = hom ≫ E.action x

@[ext] theorem FreeProductRepresentationHom.ext (G H : Type) [Monoid G] [Monoid H]
    {D E : FreeProductRepresentation (C := C) G H}
    {f g : FreeProductRepresentationHom (C := C) G H D E}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp_all

instance freeProductRepresentationCategory (G H : Type) [Monoid G] [Monoid H] :
    Category (FreeProductRepresentation (C := C) G H) where
  Hom := FreeProductRepresentationHom (C := C) G H
  id D := ⟨𝟙 D.target, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    intro x
    rw [← Category.assoc, f.intertwines, Category.assoc, g.intertwines]
    simp only [Category.assoc]⟩
  id_comp _ := by ext; simp
  comp_id _ := by ext; simp
  assoc _ _ _ := by ext; simp [Category.assoc]

def toRepresentationObj (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    FreeProductRepresentation (C := C) G H where
  target := (vertexData (C := C) G H P).leftTarget
  action := freeProductAction (C := C) G H (vertexData (C := C) G H P)

@[simp] theorem toRepresentation_action_inl (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) (g : G) :
    (toRepresentationObj (C := C) G H P).action (Monoid.Coprod.inl g) = P.left.map g := rfl

@[simp] theorem toRepresentation_action_inr (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) (h : H) :
    (toRepresentationObj (C := C) G H P).action (Monoid.Coprod.inr h) =
      P.glue.hom.app (SingleObj.star PUnit) ≫ P.right.map h ≫
      P.glue.inv.app (SingleObj.star PUnit) := by
  change freeProductAction (C := C) G H (vertexData (C := C) G H P)
      (Monoid.Coprod.inr h) =
    P.glue.hom.app (SingleObj.star PUnit) ≫ P.right.map h ≫
      P.glue.inv.app (SingleObj.star PUnit)
  rw [freeProductAction_inr]
  rfl

theorem nat_app_pointLeg_star_heq (G H : Type) [Monoid G] [Monoid H]
    {P Q : PointSpanPseudoCocone (C := C) G H} (f : P ⟶ Q) :
    HEq (f.left.app ((pointLeg G).obj (SingleObj.star PUnit.{1})))
      (f.left.app (SingleObj.star G)) := by
  rfl

/-- Transport a morphism along independently proved endpoint equalities. -/
def transportedHom {X X' Y Y' : C} (hx : X' = X) (hy : Y = Y')
    (f : X ⟶ Y) : X' ⟶ Y' := by
  subst X'
  subst Y'
  exact f

theorem eqToHom_comp_comp_eq_transportedHom
    {X X' Y Y' : C} (hx : X' = X) (hy : Y = Y') (f : X ⟶ Y) :
    eqToHom hx ≫ f ≫ eqToHom hy = transportedHom hx hy f := by
  subst X'
  subst Y'
  simp [transportedHom]

theorem eqToHom_self_bracket (X Y : C) (hx : X = X) (hy : Y = Y)
    (f : X ⟶ Y) : eqToHom hx ≫ f ≫ eqToHom hy = f := by
  cases Subsingleton.elim hx rfl
  cases Subsingleton.elim hy rfl
  simp

theorem conjugatedIntertwiner
    {X Y X' Y' : C}
    (i : X ≅ Y) (j : X' ≅ Y')
    (p : Y ⟶ Y) (q : Y' ⟶ Y')
    (l : X ⟶ X') (r : Y ⟶ Y')
    (hs : i.hom ≫ r = l ≫ j.hom)
    (hn : p ≫ r = r ≫ q) :
    (i.hom ≫ p ≫ i.inv) ≫ l =
      l ≫ (j.hom ≫ q ≫ j.inv) := by
  have hi : i.inv ≫ l = r ≫ j.inv := by
    apply (cancel_epi i.hom).1
    slice_lhs 1 2 => simp
    slice_rhs 1 2 => exact hs
    simp
  slice_lhs 3 4 => exact hi
  slice_lhs 2 3 => exact hn
  slice_lhs 1 2 => exact hs
  simp only [Category.assoc]

theorem glue_identity_bracket (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    𝟙 (P.left.obj (SingleObj.star G)) ≫
        P.glue.hom.app (SingleObj.star PUnit) ≫
        𝟙 (P.right.obj ((pointLeg H).obj (SingleObj.star PUnit))) =
      P.glue.hom.app (SingleObj.star PUnit) := by
  simp

theorem left_app_identity_bracket (G H : Type) [Monoid G] [Monoid H]
    {P Q : PointSpanPseudoCocone (C := C) G H} (f : P ⟶ Q) :
    𝟙 (P.left.obj ((pointLeg G).obj (SingleObj.star PUnit))) ≫
        f.left.app (SingleObj.star G) ≫
        𝟙 (Q.left.obj (SingleObj.star G)) =
      f.left.app (SingleObj.star G) := by
  simp

theorem exact_inr_intertwiner (G H : Type) [Monoid G] [Monoid H]
    (P Q : PointSpanPseudoCocone (C := C) G H) (f : P ⟶ Q) (h : H) :
    (P.glue.hom.app (SingleObj.star PUnit) ≫ P.right.map h ≫
        P.glue.inv.app (SingleObj.star PUnit)) ≫
        f.left.app (SingleObj.star G) =
      f.left.app (SingleObj.star G) ≫
        (Q.glue.hom.app (SingleObj.star PUnit) ≫ Q.right.map h ≫
          Q.glue.inv.app (SingleObj.star PUnit)) := by
  apply conjugatedIntertwiner
      (P.glue.app (SingleObj.star PUnit))
      (Q.glue.app (SingleObj.star PUnit))
      (P.right.map h) (Q.right.map h)
      (f.left.app (SingleObj.star G))
      (f.right.app (SingleObj.star H))
  · exact NatTrans.congr_app f.glue_naturality (SingleObj.star PUnit)
  · exact f.right.naturality h

#print axioms freeProductAction
#print axioms freeProductAction_inl
#print axioms freeProductAction_inr
#print axioms vertexData
#print axioms toRepresentationObj
#print axioms toRepresentation_action_inl
#print axioms toRepresentation_action_inr
#print axioms mappedPointLegStarIso
#print axioms eqToHom_comp_comp_eq_transportedHom
#print axioms glue_identity_bracket
#print axioms left_app_identity_bracket
#print axioms exact_inr_intertwiner

end ConstructionTargets.FreeProductPointSpanRepresentations
