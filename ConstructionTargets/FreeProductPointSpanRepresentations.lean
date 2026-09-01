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

/-- Target-change of a free-product action, preserving `End.mul_def`. -/
def mappedAction (G Hm : Type) [Monoid G] [Monoid Hm]
    {C D : Type} [Category C] [Category D] (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    Monoid.Coprod G Hm →* End (K.obj R.target) where
  toFun x := K.map (R.action x)
  map_one' := by
    rw [R.action.map_one]
    exact K.map_id _
  map_mul' x y := by
    change K.map (R.action (x * y)) =
      K.map (R.action y) ≫ K.map (R.action x)
    rw [R.action.map_mul, End.mul_def, K.map_comp]

@[simp] theorem mappedAction_apply
    (G Hm : Type) [Monoid G] [Monoid Hm]
    {C D : Type} [Category C] [Category D] (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm)
    (x : Monoid.Coprod G Hm) :
    mappedAction G Hm K R x = K.map (R.action x) := rfl

@[simp] theorem mappedAction_inl
    (G Hm : Type) [Monoid G] [Monoid Hm]
    {C D : Type} [Category C] [Category D] (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) (g : G) :
    mappedAction G Hm K R (Monoid.Coprod.inl g) =
      K.map (R.action (Monoid.Coprod.inl g)) := rfl

@[simp] theorem mappedAction_inr
    (G Hm : Type) [Monoid G] [Monoid Hm]
    {C D : Type} [Category C] [Category D] (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) (h : Hm) :
    mappedAction G Hm K R (Monoid.Coprod.inr h) =
      K.map (R.action (Monoid.Coprod.inr h)) := rfl

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

theorem inl_intertwiner (G H : Type) [Monoid G] [Monoid H]
    (P Q : PointSpanPseudoCocone (C := C) G H) (f : P ⟶ Q) (g : G) :
    (toRepresentationObj (C := C) G H P).action (Monoid.Coprod.inl g) ≫
        f.left.app (SingleObj.star G) =
      f.left.app (SingleObj.star G) ≫
        (toRepresentationObj (C := C) G H Q).action (Monoid.Coprod.inl g) := by
  change P.left.map g ≫ f.left.app (SingleObj.star G) =
    f.left.app (SingleObj.star G) ≫ Q.left.map g
  exact f.left.naturality g

theorem inr_intertwiner (G H : Type) [Monoid G] [Monoid H]
    (P Q : PointSpanPseudoCocone (C := C) G H) (f : P ⟶ Q) (h : H) :
    (toRepresentationObj (C := C) G H P).action (Monoid.Coprod.inr h) ≫
        f.left.app (SingleObj.star G) =
      f.left.app (SingleObj.star G) ≫
        (toRepresentationObj (C := C) G H Q).action (Monoid.Coprod.inr h) := by
  rw [toRepresentation_action_inr, toRepresentation_action_inr]
  exact exact_inr_intertwiner G H P Q f h

/-- A point-span morphism intertwines the induced free-product actions. The
multiplication case keeps the categorical composition order explicit. -/
theorem freeProduct_intertwiner (G H : Type) [Monoid G] [Monoid H]
    (P Q : PointSpanPseudoCocone (C := C) G H) (f : P ⟶ Q)
    (x : Monoid.Coprod G H) :
    (toRepresentationObj (C := C) G H P).action x ≫
        f.left.app (SingleObj.star G) =
      f.left.app (SingleObj.star G) ≫
        (toRepresentationObj (C := C) G H Q).action x := by
  induction x using Monoid.Coprod.induction_on with
  | inl g => exact inl_intertwiner G H P Q f g
  | inr h => exact inr_intertwiner G H P Q f h
  | mul x y hx hy =>
      simp only [map_mul, End.mul_def]
      slice_lhs 2 3 => exact hx
      exact ((reassoc_of% hy)
        ((toRepresentationObj (C := C) G H Q).action x)).trans
          (Category.assoc _ _ _)

def toRepresentationMap (G H : Type) [Monoid G] [Monoid H]
    {P Q : PointSpanPseudoCocone (C := C) G H} (f : P ⟶ Q) :
    toRepresentationObj (C := C) G H P ⟶
      toRepresentationObj (C := C) G H Q where
  hom := f.left.app (SingleObj.star G)
  intertwines := freeProduct_intertwiner G H P Q f

@[simp] theorem toRepresentationMap_hom (G H : Type) [Monoid G] [Monoid H]
    {P Q : PointSpanPseudoCocone (C := C) G H} (f : P ⟶ Q) :
    (toRepresentationMap G H f).hom = f.left.app (SingleObj.star G) := rfl

def toRepresentationFunctor (G H : Type) [Monoid G] [Monoid H] :
    PointSpanPseudoCocone (C := C) G H ⥤
      FreeProductRepresentation (C := C) G H where
  obj := toRepresentationObj (C := C) G H
  map := toRepresentationMap G H
  map_id P := by
    apply FreeProductRepresentationHom.ext
    rfl
  map_comp f g := by
    apply FreeProductRepresentationHom.ext
    rfl

@[simp] theorem toRepresentationFunctor_obj (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    (toRepresentationFunctor (C := C) G H).obj P =
      toRepresentationObj (C := C) G H P := rfl

@[simp] theorem toRepresentationFunctor_map_hom
    (G H : Type) [Monoid G] [Monoid H]
    {P Q : PointSpanPseudoCocone (C := C) G H} (f : P ⟶ Q) :
    ((toRepresentationFunctor (C := C) G H).map f).hom =
      f.left.app (SingleObj.star G) := rfl

@[simp] theorem toRepresentationFunctor_action_inl
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) (g : G) :
    ((toRepresentationFunctor (C := C) G H).obj P).action
        (Monoid.Coprod.inl g) = P.left.map g :=
  toRepresentation_action_inl G H P g

@[simp] theorem toRepresentationFunctor_action_inr
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) (h : H) :
    ((toRepresentationFunctor (C := C) G H).obj P).action
        (Monoid.Coprod.inr h) =
      P.glue.hom.app (SingleObj.star PUnit) ≫ P.right.map h ≫
        P.glue.inv.app (SingleObj.star PUnit) :=
  toRepresentation_action_inr G H P h

def restrictedLeftFunctor (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) : SingleObj G ⥤ C :=
  SingleObj.functor (R.action.comp Monoid.Coprod.inl)

def restrictedRightFunctor (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) : SingleObj H ⥤ C :=
  SingleObj.functor (R.action.comp Monoid.Coprod.inr)

@[simp] theorem restrictedLeftFunctor_obj
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    (restrictedLeftFunctor G H C R).obj (SingleObj.star G) = R.target := rfl

@[simp] theorem restrictedRightFunctor_obj
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    (restrictedRightFunctor G H C R).obj (SingleObj.star H) = R.target := rfl

@[simp] theorem restrictedLeftFunctor_map
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) (g : G) :
    (restrictedLeftFunctor G H C R).map
        (X := SingleObj.star G) (Y := SingleObj.star G) g =
      R.action (Monoid.Coprod.inl g) := rfl

@[simp] theorem restrictedRightFunctor_map
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) (h : H) :
    (restrictedRightFunctor G H C R).map
        (X := SingleObj.star H) (Y := SingleObj.star H) h =
      R.action (Monoid.Coprod.inr h) := rfl

def restrictedGlue (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    pointLeg G ⋙ restrictedLeftFunctor G H C R ≅
      pointLeg H ⋙ restrictedRightFunctor G H C R :=
  NatIso.ofComponents (fun _ => Iso.refl R.target) (by
    intro X Y f
    cases X
    cases Y
    change R.action (Monoid.Coprod.inl (pointHom G f)) ≫ 𝟙 R.target =
      𝟙 R.target ≫ R.action (Monoid.Coprod.inr (pointHom H f))
    cases f
    simp [pointHom])

@[simp] theorem restrictedGlue_hom_app
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    (restrictedGlue G H C R).hom.app (SingleObj.star PUnit) = 𝟙 R.target := rfl

@[simp] theorem restrictedGlue_inv_app
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    (restrictedGlue G H C R).inv.app (SingleObj.star PUnit) = 𝟙 R.target := rfl

def fromRepresentationObj (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    PointSpanPseudoCocone (C := C) G H where
  left := restrictedLeftFunctor G H C R
  right := restrictedRightFunctor G H C R
  glue := restrictedGlue G H C R

def restrictedLeftNatTrans
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    restrictedLeftFunctor G H C R ⟶ restrictedLeftFunctor G H C S :=
  SingleObj.natTrans f.hom (fun g => f.intertwines (Monoid.Coprod.inl g))

def restrictedRightNatTrans
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    restrictedRightFunctor G H C R ⟶ restrictedRightFunctor G H C S :=
  SingleObj.natTrans f.hom (fun h => f.intertwines (Monoid.Coprod.inr h))

@[simp] theorem restrictedLeftNatTrans_app
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    (restrictedLeftNatTrans G H C f).app (SingleObj.star G) = f.hom := rfl

@[simp] theorem restrictedRightNatTrans_app
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    (restrictedRightNatTrans G H C f).app (SingleObj.star H) = f.hom := rfl

def fromRepresentationMap
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    fromRepresentationObj G H C R ⟶ fromRepresentationObj G H C S where
  left := restrictedLeftNatTrans G H C f
  right := restrictedRightNatTrans G H C f
  glue_naturality := by
    ext X
    cases X
    change (𝟙 R.target) ≫ f.hom = f.hom ≫ (𝟙 S.target)
    simp

def fromRepresentationFunctor
    (G H C : Type) [Monoid G] [Monoid H] [Category C] :
    FreeProductRepresentation (C := C) G H ⥤
      PointSpanPseudoCocone (C := C) G H where
  obj := fromRepresentationObj G H C
  map := fromRepresentationMap G H C
  map_id R := by
    apply ConstructionTargets.GenericSpanPseudoCoconeTransport.SpanPseudoCoconeHom.ext
    · ext X; cases X; rfl
    · ext X; cases X; rfl
  map_comp f g := by
    apply ConstructionTargets.GenericSpanPseudoCoconeTransport.SpanPseudoCoconeHom.ext
    · ext X; cases X; rfl
    · ext X; cases X; rfl

theorem representation_roundTrip_action
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    (toRepresentationObj (C := C) G H
      (fromRepresentationObj G H C R)).action = R.action := by
  apply Monoid.Coprod.hom_ext
  · ext g
    rw [MonoidHom.comp_apply, toRepresentation_action_inl]
    rfl
  · ext h
    rw [MonoidHom.comp_apply, toRepresentation_action_inr]
    change 𝟙 R.target ≫ R.action (Monoid.Coprod.inr h) ≫ 𝟙 R.target =
      R.action (Monoid.Coprod.inr h)
    simp

@[simp] theorem representation_roundTrip_target
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    (toRepresentationObj (C := C) G H
      (fromRepresentationObj G H C R)).target = R.target := rfl

@[simp] theorem representation_roundTrip_map_hom
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    (fromRepresentationMap G H C f).left.app (SingleObj.star G) = f.hom := rfl

@[simp] theorem cocone_roundTrip_left_map
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (P : PointSpanPseudoCocone (C := C) G H) (g : G) :
    (fromRepresentationObj G H C (toRepresentationObj (C := C) G H P)).left.map
        (X := SingleObj.star G) (Y := SingleObj.star G) g =
      P.left.map (X := SingleObj.star G) (Y := SingleObj.star G) g := by
  change (toRepresentationObj (C := C) G H P).action
    (Monoid.Coprod.inl g) = P.left.map g
  exact toRepresentation_action_inl G H P g

@[simp] theorem cocone_roundTrip_right_map
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (P : PointSpanPseudoCocone (C := C) G H) (h : H) :
    (fromRepresentationObj G H C (toRepresentationObj (C := C) G H P)).right.map
        (X := SingleObj.star H) (Y := SingleObj.star H) h =
      P.glue.hom.app (SingleObj.star PUnit) ≫
        P.right.map (X := SingleObj.star H) (Y := SingleObj.star H) h ≫
        P.glue.inv.app (SingleObj.star PUnit) := by
  change (toRepresentationObj (C := C) G H P).action
    (Monoid.Coprod.inr h) = _
  exact toRepresentation_action_inr G H P h

@[simp] theorem cocone_roundTrip_glue_hom
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (P : PointSpanPseudoCocone (C := C) G H) :
    (fromRepresentationObj G H C
      (toRepresentationObj (C := C) G H P)).glue.hom.app
        (SingleObj.star PUnit) = 𝟙 _ := rfl

variable {C : Type} [Category C]

theorem comp_inv_eq_inv_comp_conjugate {X Y : C}
    (i : X ≅ Y) (p : Y ⟶ Y) :
    p ≫ i.inv = i.inv ≫ (i.hom ≫ p ≫ i.inv) := by
  slice_rhs 1 2 => simp
  simp

theorem conjugate_comp_hom_eq_hom_comp {X Y : C}
    (i : X ≅ Y) (p : Y ⟶ Y) :
    (i.hom ≫ p ≫ i.inv) ≫ i.hom = i.hom ≫ p := by
  slice_lhs 3 4 => simp
  simp

theorem mapped_pointLeg_star_proof_eq_rfl
    (M : Type) [Monoid M] (F : SingleObj M ⥤ C) :
    mapped_pointLeg_star_eq (C := C) M F = rfl := Subsingleton.elim _ _

theorem mapped_pointLeg_star_symm_proof_eq_rfl
    (M : Type) [Monoid M] (F : SingleObj M ⥤ C) :
    (mapped_pointLeg_star_eq (C := C) M F).symm = rfl := Subsingleton.elim _ _

def rightToLeftComponent
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    P.right.obj (SingleObj.star H) ⟶ P.left.obj (SingleObj.star G) :=
  eqToHom (mapped_pointLeg_star_eq (C := C) H P.right).symm ≫
    P.glue.inv.app (SingleObj.star PUnit) ≫
    eqToHom (mapped_pointLeg_star_eq (C := C) G P.left)

def leftToRightComponent
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    P.left.obj (SingleObj.star G) ⟶ P.right.obj (SingleObj.star H) :=
  eqToHom (mapped_pointLeg_star_eq (C := C) G P.left).symm ≫
    P.glue.hom.app (SingleObj.star PUnit) ≫
    eqToHom (mapped_pointLeg_star_eq (C := C) H P.right)

theorem rightToLeftComponent_eq_glue_inv
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    rightToLeftComponent G H P = P.glue.inv.app (SingleObj.star PUnit) := by
  unfold rightToLeftComponent
  exact eqToHom_self_bracket _ _ _ _ _

theorem leftToRightComponent_eq_glue_hom
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    leftToRightComponent G H P = P.glue.hom.app (SingleObj.star PUnit) := by
  unfold leftToRightComponent
  exact eqToHom_self_bracket _ _ _ _ _

theorem rightToLeft_naturality
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) (h : H) :
    P.right.map h ≫ rightToLeftComponent G H P =
      rightToLeftComponent G H P ≫
        (fromRepresentationObj G H C
          (toRepresentationObj (C := C) G H P)).right.map
            (X := SingleObj.star H) (Y := SingleObj.star H) h := by
  rw [rightToLeftComponent_eq_glue_inv, cocone_roundTrip_right_map]
  exact comp_inv_eq_inv_comp_conjugate
    (P.glue.app (SingleObj.star PUnit)) (P.right.map h)

theorem leftToRight_naturality
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) (h : H) :
    (fromRepresentationObj G H C
        (toRepresentationObj (C := C) G H P)).right.map
          (X := SingleObj.star H) (Y := SingleObj.star H) h ≫
        leftToRightComponent G H P =
      leftToRightComponent G H P ≫ P.right.map h := by
  rw [leftToRightComponent_eq_glue_hom, cocone_roundTrip_right_map]
  exact conjugate_comp_hom_eq_hom_comp
    (P.glue.app (SingleObj.star PUnit)) (P.right.map h)

def rightToLeftNatTrans
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    P.right ⟶
      (fromRepresentationObj G H C
        (toRepresentationObj (C := C) G H P)).right :=
  SingleObj.natTrans (rightToLeftComponent G H P)
    (rightToLeft_naturality G H P)

def leftToRightNatTrans
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    (fromRepresentationObj G H C
      (toRepresentationObj (C := C) G H P)).right ⟶ P.right :=
  SingleObj.natTrans (leftToRightComponent G H P)
    (leftToRight_naturality G H P)

def coconeUnitHom
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    P ⟶ (toRepresentationFunctor (C := C) G H ⋙
      fromRepresentationFunctor G H C).obj P where
  left := 𝟙 P.left
  right := rightToLeftNatTrans G H P
  glue_naturality := by
    ext X
    cases X
    change P.glue.hom.app (SingleObj.star PUnit) ≫
      rightToLeftComponent G H P = 𝟙 _ ≫ 𝟙 _
    rw [rightToLeftComponent_eq_glue_inv]
    simpa only [Category.comp_id] using
      P.glue.hom_inv_id_app (SingleObj.star PUnit)

def coconeUnitInv
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    (toRepresentationFunctor (C := C) G H ⋙
      fromRepresentationFunctor G H C).obj P ⟶ P where
  left := 𝟙 P.left
  right := leftToRightNatTrans G H P
  glue_naturality := by
    ext X
    cases X
    change 𝟙 _ ≫ leftToRightComponent G H P =
      𝟙 _ ≫ P.glue.hom.app (SingleObj.star PUnit)
    rw [leftToRightComponent_eq_glue_hom]
    rfl

def coconeUnitIsoApp
    (G H : Type) [Monoid G] [Monoid H]
    (P : PointSpanPseudoCocone (C := C) G H) :
    P ≅ (toRepresentationFunctor (C := C) G H ⋙
      fromRepresentationFunctor G H C).obj P where
  hom := coconeUnitHom G H P
  inv := coconeUnitInv G H P
  hom_inv_id := by
    apply SpanPseudoCoconeHom.ext
    · ext X
      cases X
      change (𝟙 _ ≫ 𝟙 _) = 𝟙 _
      simp
    · ext X
      cases X
      change rightToLeftComponent G H P ≫ leftToRightComponent G H P = 𝟙 _
      rw [rightToLeftComponent_eq_glue_inv, leftToRightComponent_eq_glue_hom]
      exact P.glue.inv_hom_id_app (SingleObj.star PUnit)
  inv_hom_id := by
    apply SpanPseudoCoconeHom.ext
    · ext X
      cases X
      change (𝟙 _ ≫ 𝟙 _) = 𝟙 _
      simp
    · ext X
      cases X
      change leftToRightComponent G H P ≫ rightToLeftComponent G H P = 𝟙 _
      rw [rightToLeftComponent_eq_glue_inv, leftToRightComponent_eq_glue_hom]
      exact P.glue.hom_inv_id_app (SingleObj.star PUnit)

theorem coconeUnitIso_naturality
    (G H : Type) [Monoid G] [Monoid H]
    {P Q : PointSpanPseudoCocone (C := C) G H} (f : P ⟶ Q) :
    f ≫ (coconeUnitIsoApp G H Q).hom =
      (coconeUnitIsoApp G H P).hom ≫
        (toRepresentationFunctor (C := C) G H ⋙
          fromRepresentationFunctor G H C).map f := by
  apply SpanPseudoCoconeHom.ext
  · ext X
    cases X
    change f.left.app (SingleObj.star G) ≫ 𝟙 _ =
      𝟙 _ ≫ f.left.app (SingleObj.star G)
    simp
  · ext X
    cases X
    change f.right.app (SingleObj.star H) ≫ rightToLeftComponent G H Q =
      rightToLeftComponent G H P ≫ f.left.app (SingleObj.star G)
    rw [rightToLeftComponent_eq_glue_inv, rightToLeftComponent_eq_glue_inv]
    have hs := NatTrans.congr_app f.glue_naturality (SingleObj.star PUnit)
    change P.glue.hom.app (SingleObj.star PUnit) ≫
      f.right.app (SingleObj.star H) =
        f.left.app (SingleObj.star G) ≫
          Q.glue.hom.app (SingleObj.star PUnit) at hs
    apply ((P.glue.app (SingleObj.star PUnit)).eq_inv_comp).2
    change P.glue.hom.app (SingleObj.star PUnit) ≫
      (f.right.app (SingleObj.star H) ≫
        Q.glue.inv.app (SingleObj.star PUnit)) =
          f.left.app (SingleObj.star G)
    rw [← Category.assoc]
    apply ((Q.glue.app (SingleObj.star PUnit)).comp_inv_eq).2
    simpa only [Category.assoc] using hs

def coconeUnitNatIso
    (G H : Type) [Monoid G] [Monoid H] :
    Functor.id (PointSpanPseudoCocone (C := C) G H) ≅
      toRepresentationFunctor (C := C) G H ⋙
        fromRepresentationFunctor G H C :=
  NatIso.ofComponents (coconeUnitIsoApp G H) (fun f =>
    coconeUnitIso_naturality G H f)

def representationCounitHom
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    ((fromRepresentationFunctor G H C) ⋙
      (toRepresentationFunctor (C := C) G H)).obj R ⟶ R where
  hom := 𝟙 R.target
  intertwines x := by
    change (toRepresentationObj (C := C) G H
        (fromRepresentationObj G H C R)).action x ≫ 𝟙 R.target =
      𝟙 R.target ≫ R.action x
    have ha := DFunLike.congr_fun (representation_roundTrip_action G H C R) x
    rw [ha]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

def representationCounitInv
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    R ⟶ ((fromRepresentationFunctor G H C) ⋙
      (toRepresentationFunctor (C := C) G H)).obj R where
  hom := 𝟙 R.target
  intertwines x := by
    change R.action x ≫ 𝟙 R.target = 𝟙 R.target ≫
      (toRepresentationObj (C := C) G H
        (fromRepresentationObj G H C R)).action x
    have ha := DFunLike.congr_fun (representation_roundTrip_action G H C R) x
    rw [ha]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

def representationCounitIsoApp
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    ((fromRepresentationFunctor G H C) ⋙
      (toRepresentationFunctor (C := C) G H)).obj R ≅ R where
  hom := representationCounitHom G H C R
  inv := representationCounitInv G H C R
  hom_inv_id := by
    apply FreeProductRepresentationHom.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply FreeProductRepresentationHom.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

theorem representationCounitIso_naturality
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    ((fromRepresentationFunctor G H C ⋙
      toRepresentationFunctor (C := C) G H).map f) ≫
        (representationCounitIsoApp G H C S).hom =
      (representationCounitIsoApp G H C R).hom ≫ f := by
  apply FreeProductRepresentationHom.ext
  change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
  simp

def representationCounitNatIso
    (G H C : Type) [Monoid G] [Monoid H] [Category C] :
    fromRepresentationFunctor G H C ⋙
        toRepresentationFunctor (C := C) G H ≅
      𝟭 (FreeProductRepresentation (C := C) G H) :=
  NatIso.ofComponents (representationCounitIsoApp G H C) (fun f =>
    representationCounitIso_naturality G H C f)

theorem pointSpan_triangle
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (P : PointSpanPseudoCocone (C := C) G H) :
    (toRepresentationFunctor (C := C) G H).map
        ((coconeUnitNatIso (C := C) G H).hom.app P) ≫
      (representationCounitNatIso G H C).hom.app
        ((toRepresentationFunctor (C := C) G H).obj P) =
      𝟙 ((toRepresentationFunctor (C := C) G H).obj P) := by
  apply FreeProductRepresentationHom.ext
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp

/-- Point-span pseudococones over the point legs are categorically equivalent
to representations of the ordered free product `Monoid.Coprod G H`. -/
def freeProductPointSpanEquivalence
    (G H C : Type) [Monoid G] [Monoid H] [Category C] :
    PointSpanPseudoCocone (C := C) G H ≌
      FreeProductRepresentation (C := C) G H :=
  CategoryTheory.Equivalence.mk'
    (toRepresentationFunctor (C := C) G H)
    (fromRepresentationFunctor G H C)
    (coconeUnitNatIso (C := C) G H)
    (representationCounitNatIso G H C)
    (pointSpan_triangle G H C)

@[simp] theorem equivalence_functor
    (G H C : Type) [Monoid G] [Monoid H] [Category C] :
    (freeProductPointSpanEquivalence G H C).functor =
      toRepresentationFunctor (C := C) G H := rfl

@[simp] theorem equivalence_inverse
    (G H C : Type) [Monoid G] [Monoid H] [Category C] :
    (freeProductPointSpanEquivalence G H C).inverse =
      fromRepresentationFunctor G H C := rfl

@[simp] theorem equivalence_unit_hom_left_app
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (P : PointSpanPseudoCocone (C := C) G H) :
    ((freeProductPointSpanEquivalence G H C).unitIso.hom.app P).left.app
      (SingleObj.star G) = 𝟙 _ := rfl

@[simp] theorem equivalence_unit_hom_right_app
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (P : PointSpanPseudoCocone (C := C) G H) :
    ((freeProductPointSpanEquivalence G H C).unitIso.hom.app P).right.app
      (SingleObj.star H) = rightToLeftComponent G H P := rfl

@[simp] theorem equivalence_counit_hom
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (R : FreeProductRepresentation (C := C) G H) :
    ((freeProductPointSpanEquivalence G H C).counitIso.hom.app R).hom =
      𝟙 R.target := rfl

@[simp] theorem equivalence_action_inl
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (P : PointSpanPseudoCocone (C := C) G H) (g : G) :
    ((freeProductPointSpanEquivalence G H C).functor.obj P).action
      (Monoid.Coprod.inl g) = P.left.map g :=
  toRepresentation_action_inl G H P g

@[simp] theorem equivalence_action_inr
    (G H C : Type) [Monoid G] [Monoid H] [Category C]
    (P : PointSpanPseudoCocone (C := C) G H) (h : H) :
    ((freeProductPointSpanEquivalence G H C).functor.obj P).action
      (Monoid.Coprod.inr h) =
        P.glue.hom.app (SingleObj.star PUnit) ≫ P.right.map h ≫
          P.glue.inv.app (SingleObj.star PUnit) :=
  toRepresentation_action_inr G H P h

section TargetNaturality

variable (G Hm : Type) [Monoid G] [Monoid Hm]
variable {C D : Type} [Category C] [Category D]

def postcomposePointSpanFunctor (K : C ⥤ D) :
    PointSpanPseudoCocone (C := C) G Hm ⥤ PointSpanPseudoCocone (C := D) G Hm :=
  postcomposeFunctor K

def postcomposeRepresentationObj (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    FreeProductRepresentation (C := D) G Hm where
  target := K.obj R.target
  action := mappedAction G Hm K R

def postcomposeRepresentationMap (K : C ⥤ D)
    {R S : FreeProductRepresentation (C := C) G Hm} (f : R ⟶ S) :
    postcomposeRepresentationObj G Hm K R ⟶ postcomposeRepresentationObj G Hm K S where
  hom := K.map f.hom
  intertwines x := by
    change K.map (R.action x) ≫ K.map f.hom = K.map f.hom ≫ K.map (S.action x)
    rw [← K.map_comp, ← K.map_comp, f.intertwines]

def postcomposeRepresentationFunctor (K : C ⥤ D) :
    FreeProductRepresentation (C := C) G Hm ⥤ FreeProductRepresentation (C := D) G Hm where
  obj := postcomposeRepresentationObj G Hm K
  map := postcomposeRepresentationMap G Hm K
  map_id R := by apply FreeProductRepresentationHom.ext; exact K.map_id _
  map_comp f g := by apply FreeProductRepresentationHom.ext; exact K.map_comp _ _

theorem forward_postcompose_action_eq (K : C ⥤ D)
    (P : PointSpanPseudoCocone (C := C) G Hm) :
    (toRepresentationObj (C := D) G Hm
      ((postcomposePointSpanFunctor G Hm K).obj P)).action =
    (postcomposeRepresentationObj G Hm K
      (toRepresentationObj (C := C) G Hm P)).action := by
  apply Monoid.Coprod.hom_ext
  · ext g
    change K.map (P.left.map g) = K.map (P.left.map g)
    rfl
  · ext h
    change K.map (P.glue.hom.app (SingleObj.star PUnit)) ≫ K.map (P.right.map h) ≫
        K.map (P.glue.inv.app (SingleObj.star PUnit)) =
      K.map (P.glue.hom.app (SingleObj.star PUnit) ≫ P.right.map h ≫
        P.glue.inv.app (SingleObj.star PUnit))
    rw [K.map_comp, K.map_comp]

def forwardPostcomposeIsoApp (K : C ⥤ D)
    (P : PointSpanPseudoCocone (C := C) G Hm) :
    (postcomposePointSpanFunctor G Hm K ⋙
      toRepresentationFunctor (C := D) G Hm).obj P ≅
    (toRepresentationFunctor (C := C) G Hm ⋙
      postcomposeRepresentationFunctor G Hm K).obj P where
  hom := ⟨𝟙 _, by
    intro x
    change (toRepresentationObj (C := D) G Hm
        ((postcomposePointSpanFunctor G Hm K).obj P)).action x ≫ 𝟙 _ =
      𝟙 _ ≫ (postcomposeRepresentationObj G Hm K
        (toRepresentationObj (C := C) G Hm P)).action x
    simpa only [Category.comp_id, Category.id_comp] using
      DFunLike.congr_fun (forward_postcompose_action_eq G Hm K P) x⟩
  inv := ⟨𝟙 _, by
    intro x
    change (postcomposeRepresentationObj G Hm K
        (toRepresentationObj (C := C) G Hm P)).action x ≫ 𝟙 _ =
      𝟙 _ ≫ (toRepresentationObj (C := D) G Hm
        ((postcomposePointSpanFunctor G Hm K).obj P)).action x
    simpa only [Category.comp_id, Category.id_comp] using
      (DFunLike.congr_fun (forward_postcompose_action_eq G Hm K P) x).symm⟩
  hom_inv_id := by
    apply FreeProductRepresentationHom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply FreeProductRepresentationHom.ext
    exact Category.id_comp _

theorem forwardPostcomposeIso_naturality (K : C ⥤ D)
    {P Q : PointSpanPseudoCocone (C := C) G Hm} (f : P ⟶ Q) :
    (postcomposePointSpanFunctor G Hm K ⋙
      toRepresentationFunctor (C := D) G Hm).map f ≫
        (forwardPostcomposeIsoApp G Hm K Q).hom =
    (forwardPostcomposeIsoApp G Hm K P).hom ≫
      (toRepresentationFunctor (C := C) G Hm ⋙
        postcomposeRepresentationFunctor G Hm K).map f := by
  apply FreeProductRepresentationHom.ext
  change K.map (f.left.app (SingleObj.star G)) ≫ 𝟙 _ =
    𝟙 _ ≫ K.map (f.left.app (SingleObj.star G))
  simp

def toRepresentationPostcomposeIso (K : C ⥤ D) :
    postcomposePointSpanFunctor G Hm K ⋙ toRepresentationFunctor (C := D) G Hm ≅
      toRepresentationFunctor (C := C) G Hm ⋙
        postcomposeRepresentationFunctor G Hm K :=
  NatIso.ofComponents (forwardPostcomposeIsoApp G Hm K)
    (fun f => forwardPostcomposeIso_naturality G Hm K f)

def equivalenceFunctorPostcomposeIso (K : C ⥤ D) :=
  toRepresentationPostcomposeIso G Hm K

@[simp] theorem forward_component_hom (K : C ⥤ D)
    (P : PointSpanPseudoCocone (C := C) G Hm) :
    ((toRepresentationPostcomposeIso G Hm K).hom.app P).hom = 𝟙 _ := rfl

/-- Restriction of a mapped coproduct action agrees, with explicit identity
components, with postcomposition of the restricted original action. -/
def restrictionPostcomposeIso (M : Type) [Monoid M]
    (ι : M →* Monoid.Coprod G Hm) (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    SingleObj.functor ((mappedAction G Hm K R).comp ι) ≅
      SingleObj.functor (R.action.comp ι) ⋙ K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    cases X
    cases Y
    change K.map (R.action (ι f)) ≫ 𝟙 _ = 𝟙 _ ≫ K.map (R.action (ι f))
    simp)

def reverseLeftComparison (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    ((postcomposeRepresentationFunctor G Hm K ⋙
      fromRepresentationFunctor G Hm D).obj R).left ≅
    ((fromRepresentationFunctor G Hm C ⋙
      postcomposePointSpanFunctor G Hm K).obj R).left :=
  restrictionPostcomposeIso G Hm G Monoid.Coprod.inl K R

def reverseRightComparison (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    ((postcomposeRepresentationFunctor G Hm K ⋙
      fromRepresentationFunctor G Hm D).obj R).right ≅
    ((fromRepresentationFunctor G Hm C ⋙
      postcomposePointSpanFunctor G Hm K).obj R).right :=
  restrictionPostcomposeIso G Hm Hm Monoid.Coprod.inr K R

def reversePostcomposeIsoApp (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    (postcomposeRepresentationFunctor G Hm K ⋙
      fromRepresentationFunctor G Hm D).obj R ≅
    (fromRepresentationFunctor G Hm C ⋙
      postcomposePointSpanFunctor G Hm K).obj R where
  hom := {
    left := (reverseLeftComparison G Hm K R).hom
    right := (reverseRightComparison G Hm K R).hom
    glue_naturality := by
      ext X
      cases X
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ K.map (𝟙 R.target)
      simp }
  inv := {
    left := (reverseLeftComparison G Hm K R).inv
    right := (reverseRightComparison G Hm K R).inv
    glue_naturality := by
      ext X
      cases X
      change K.map (𝟙 R.target) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      simp }
  hom_inv_id := by
    apply SpanPseudoCoconeHom.ext
    · ext X; cases X; exact Category.id_comp _
    · ext X; cases X; exact Category.id_comp _
  inv_hom_id := by
    apply SpanPseudoCoconeHom.ext
    · ext X; cases X; exact Category.id_comp _
    · ext X; cases X; exact Category.id_comp _

theorem reversePostcomposeIso_naturality (K : C ⥤ D)
    {R S : FreeProductRepresentation (C := C) G Hm} (f : R ⟶ S) :
    (postcomposeRepresentationFunctor G Hm K ⋙
        fromRepresentationFunctor G Hm D).map f ≫
      (reversePostcomposeIsoApp G Hm K S).hom =
    (reversePostcomposeIsoApp G Hm K R).hom ≫
      (fromRepresentationFunctor G Hm C ⋙
        postcomposePointSpanFunctor G Hm K).map f := by
  apply SpanPseudoCoconeHom.ext
  · ext X
    cases X
    change K.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ K.map f.hom
    simp
  · ext X
    cases X
    change K.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ K.map f.hom
    simp

def fromRepresentationPostcomposeIso (K : C ⥤ D) :
    postcomposeRepresentationFunctor G Hm K ⋙
        fromRepresentationFunctor G Hm D ≅
      fromRepresentationFunctor G Hm C ⋙
        postcomposePointSpanFunctor G Hm K :=
  NatIso.ofComponents (reversePostcomposeIsoApp G Hm K)
    (fun f => reversePostcomposeIso_naturality G Hm K f)

def equivalenceInversePostcomposeIso (K : C ⥤ D) :=
  fromRepresentationPostcomposeIso G Hm K

@[simp] theorem restrictionPostcomposeIso_hom_app (M : Type) [Monoid M]
    (ι : M →* Monoid.Coprod G Hm) (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    (restrictionPostcomposeIso G Hm M ι K R).hom.app (SingleObj.star M) = 𝟙 _ := rfl

@[simp] theorem reverse_component_left_app (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    ((fromRepresentationPostcomposeIso G Hm K).hom.app R).left.app
      (SingleObj.star G) = 𝟙 _ := rfl

@[simp] theorem reverse_component_right_app (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G Hm) :
    ((fromRepresentationPostcomposeIso G Hm K).hom.app R).right.app
      (SingleObj.star Hm) = 𝟙 _ := rfl

end TargetNaturality

#print axioms freeProductAction
#print axioms freeProductAction_inl
#print axioms freeProductAction_inr
#print axioms mappedAction
#print axioms mappedAction_apply
#print axioms vertexData
#print axioms toRepresentationObj
#print axioms toRepresentation_action_inl
#print axioms toRepresentation_action_inr
#print axioms mappedPointLegStarIso
#print axioms eqToHom_comp_comp_eq_transportedHom
#print axioms glue_identity_bracket
#print axioms left_app_identity_bracket
#print axioms exact_inr_intertwiner
#print axioms inl_intertwiner
#print axioms inr_intertwiner
#print axioms freeProduct_intertwiner
#print axioms toRepresentationMap
#print axioms toRepresentationFunctor
#print axioms restrictedGlue
#print axioms fromRepresentationObj
#print axioms fromRepresentationMap
#print axioms fromRepresentationFunctor
#print axioms representation_roundTrip_action
#print axioms cocone_roundTrip_right_map
#print axioms rightToLeftComponent_eq_glue_inv
#print axioms leftToRightComponent_eq_glue_hom
#print axioms rightToLeft_naturality
#print axioms leftToRight_naturality
#print axioms coconeUnitNatIso
#print axioms representationCounitNatIso
#print axioms pointSpan_triangle
#print axioms freeProductPointSpanEquivalence
#print axioms equivalence_action_inl
#print axioms equivalence_action_inr
#print axioms postcomposeRepresentationFunctor
#print axioms toRepresentationPostcomposeIso
#print axioms equivalenceFunctorPostcomposeIso
#print axioms restrictionPostcomposeIso
#print axioms fromRepresentationPostcomposeIso
#print axioms equivalenceInversePostcomposeIso

end ConstructionTargets.FreeProductPointSpanRepresentations
