import ConstructionTargets.FreeProductPointSpanRepresentations

open CategoryTheory
noncomputable section

namespace ConstructionTargets.FreeProductRepresentationSingleObjEquivalence

open ConstructionTargets.FreeProductPointSpanRepresentations

variable (G H : Type) [Monoid G] [Monoid H]
variable {C D : Type} [Category C] [Category D]
abbrev M := Monoid.Coprod G H

def representationToFunctorObj
    (R : FreeProductRepresentation (C := C) G H) : SingleObj (M G H) ⥤ C :=
  SingleObj.functor R.action

def representationToFunctorMap {R S : FreeProductRepresentation (C := C) G H}
    (f : R ⟶ S) : representationToFunctorObj G H R ⟶ representationToFunctorObj G H S :=
  SingleObj.natTrans f.hom f.intertwines

def representationToFunctor :
    FreeProductRepresentation (C := C) G H ⥤ (SingleObj (M G H) ⥤ C) where
  obj := representationToFunctorObj G H
  map := representationToFunctorMap G H
  map_id _ := by ext X; cases X; rfl
  map_comp _ _ := by ext X; cases X; rfl

def extractedAction (F : SingleObj (M G H) ⥤ C) :
    M G H →* End (F.obj (SingleObj.star (M G H))) where
  toFun x := F.map x
  map_one' := F.map_id _
  map_mul' x y := by
    rw [End.mul_def, ← F.map_comp, SingleObj.comp_as_mul]

def functorToRepresentationObj (F : SingleObj (M G H) ⥤ C) :
    FreeProductRepresentation (C := C) G H where
  target := F.obj (SingleObj.star (M G H))
  action := extractedAction G H F

def functorToRepresentationMap {F Q : SingleObj (M G H) ⥤ C} (τ : F ⟶ Q) :
    functorToRepresentationObj G H F ⟶ functorToRepresentationObj G H Q where
  hom := τ.app (SingleObj.star (M G H))
  intertwines x := τ.naturality x

def functorToRepresentation :
    (SingleObj (M G H) ⥤ C) ⥤ FreeProductRepresentation (C := C) G H where
  obj := functorToRepresentationObj G H
  map := functorToRepresentationMap G H
  map_id _ := by apply FreeProductRepresentationHom.ext; rfl
  map_comp _ _ := by apply FreeProductRepresentationHom.ext; rfl

def representationRoundTripIso (R : FreeProductRepresentation (C := C) G H) :
    ((representationToFunctor G H) ⋙ (functorToRepresentation G H)).obj R ≅ R where
  hom := ⟨𝟙 _, by intro x; change R.action x ≫ 𝟙 _ = 𝟙 _ ≫ R.action x; simp⟩
  inv := ⟨𝟙 _, by intro x; change R.action x ≫ 𝟙 _ = 𝟙 _ ≫ R.action x; simp⟩
  hom_inv_id := by
    apply FreeProductRepresentationHom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply FreeProductRepresentationHom.ext
    exact Category.id_comp _

def functorRoundTripIso (F : SingleObj (M G H) ⥤ C) :
    ((functorToRepresentation G H) ⋙ (representationToFunctor G H)).obj F ≅ F :=
  NatIso.ofComponents (fun X => by cases X; exact Iso.refl _) (by
    intro X Y f; cases X; cases Y
    change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    simp)

def representationRoundTripNatIso :
    representationToFunctor (C := C) G H ⋙ functorToRepresentation G H ≅
      𝟭 (FreeProductRepresentation (C := C) G H) :=
  NatIso.ofComponents (representationRoundTripIso G H) (by
    intro R S f; apply FreeProductRepresentationHom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom; simp)

def functorRoundTripNatIso :
    functorToRepresentation (C := C) G H ⋙ representationToFunctor G H ≅
      𝟭 (SingleObj (M G H) ⥤ C) :=
  NatIso.ofComponents (functorRoundTripIso G H) (by
    intro F Q τ; ext X; cases X
    change τ.app (SingleObj.star (M G H)) ≫ 𝟙 _ =
      𝟙 _ ≫ τ.app (SingleObj.star (M G H)); simp)

theorem triangle (R : FreeProductRepresentation (C := C) G H) :
    (representationToFunctor G H).map
        ((representationRoundTripNatIso (C := C) G H).symm.hom.app R) ≫
      (functorRoundTripNatIso (C := C) G H).hom.app
        ((representationToFunctor G H).obj R) =
      𝟙 ((representationToFunctor G H).obj R) := by
  ext X; cases X
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp

def representationSingleObjEquivalence :
    FreeProductRepresentation (C := C) G H ≌ (SingleObj (M G H) ⥤ C) :=
  Equivalence.mk' (representationToFunctor G H) (functorToRepresentation G H)
    (representationRoundTripNatIso (C := C) G H).symm
    (functorRoundTripNatIso (C := C) G H) (triangle G H)

def postcomposeRepresentationObj (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G H) :
    FreeProductRepresentation (C := D) G H where
  target := K.obj R.target
  action := mappedAction G H K R

def postcomposeRepresentationMap (K : C ⥤ D)
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    postcomposeRepresentationObj G H K R ⟶ postcomposeRepresentationObj G H K S where
  hom := K.map f.hom
  intertwines x := by
    change K.map (R.action x) ≫ K.map f.hom = K.map f.hom ≫ K.map (S.action x)
    rw [← K.map_comp, ← K.map_comp, f.intertwines]

def postcomposeRepresentationFunctor (K : C ⥤ D) :
    FreeProductRepresentation (C := C) G H ⥤ FreeProductRepresentation (C := D) G H where
  obj := postcomposeRepresentationObj G H K
  map := postcomposeRepresentationMap G H K
  map_id R := by apply FreeProductRepresentationHom.ext; exact K.map_id _
  map_comp f g := by apply FreeProductRepresentationHom.ext; exact K.map_comp _ _

def representationToFunctorPostcomposeIso (K : C ⥤ D) :
    postcomposeRepresentationFunctor G H K ⋙ representationToFunctor G H ≅
      representationToFunctor G H ⋙
        (Functor.whiskeringRight (SingleObj (M G H)) C D).obj K :=
  NatIso.ofComponents (fun R =>
    NatIso.ofComponents (fun X => by cases X; exact Iso.refl _) (by
      intro X Y f; cases X; cases Y
      change K.map (R.action f) ≫ 𝟙 _ = 𝟙 _ ≫ K.map (R.action f); simp)) (by
    intro R S f; ext X; cases X
    change K.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ K.map f.hom; simp)

theorem inverse_postcompose_action_eq (K : C ⥤ D)
    (F : SingleObj (M G H) ⥤ C) :
    (functorToRepresentationObj G H (F ⋙ K)).action =
      (postcomposeRepresentationObj G H K (functorToRepresentationObj G H F)).action := rfl

def functorToRepresentationPostcomposeIsoApp (K : C ⥤ D)
    (F : SingleObj (M G H) ⥤ C) :
    ((Functor.whiskeringRight (SingleObj (M G H)) C D).obj K ⋙
        functorToRepresentation G H).obj F ≅
      (functorToRepresentation G H ⋙ postcomposeRepresentationFunctor G H K).obj F where
  hom := ⟨𝟙 _, by
    intro x
    change (functorToRepresentationObj G H (F ⋙ K)).action x ≫ 𝟙 _ =
      𝟙 _ ≫ (postcomposeRepresentationObj G H K
        (functorToRepresentationObj G H F)).action x
    simpa only [Category.comp_id, Category.id_comp] using
      DFunLike.congr_fun (inverse_postcompose_action_eq G H K F) x⟩
  inv := ⟨𝟙 _, by
    intro x
    change (postcomposeRepresentationObj G H K
        (functorToRepresentationObj G H F)).action x ≫ 𝟙 _ =
      𝟙 _ ≫ (functorToRepresentationObj G H (F ⋙ K)).action x
    simpa only [Category.comp_id, Category.id_comp] using
      (DFunLike.congr_fun (inverse_postcompose_action_eq G H K F) x).symm⟩
  hom_inv_id := by apply FreeProductRepresentationHom.ext; exact Category.id_comp _
  inv_hom_id := by apply FreeProductRepresentationHom.ext; exact Category.id_comp _

def functorToRepresentationPostcomposeIso (K : C ⥤ D) :
    (Functor.whiskeringRight (SingleObj (M G H)) C D).obj K ⋙
        functorToRepresentation G H ≅
      functorToRepresentation G H ⋙ postcomposeRepresentationFunctor G H K :=
  NatIso.ofComponents (functorToRepresentationPostcomposeIsoApp G H K) (by
      intro F Q τ; apply FreeProductRepresentationHom.ext
      change K.map (τ.app (SingleObj.star (M G H))) ≫ 𝟙 _ =
        𝟙 _ ≫ K.map (τ.app (SingleObj.star (M G H))); simp)

@[simp] theorem representationToFunctor_obj_map
    (R : FreeProductRepresentation (C := C) G H) (x : M G H) :
    ((representationToFunctor G H).obj R).map
      (X := SingleObj.star (M G H)) (Y := SingleObj.star (M G H)) x =
      R.action x := rfl

@[simp] theorem functorToRepresentation_action (F : SingleObj (M G H) ⥤ C)
    (x : M G H) : (functorToRepresentationObj G H F).action x = F.map x := rfl

@[simp] theorem representationToFunctor_map_app
    {R S : FreeProductRepresentation (C := C) G H} (f : R ⟶ S) :
    ((representationToFunctor G H).map f).app (SingleObj.star (M G H)) = f.hom := rfl

@[simp] theorem forwardPostcompose_hom_app_star (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G H) :
    ((representationToFunctorPostcomposeIso G H K).hom.app R).app
      (SingleObj.star (M G H)) = 𝟙 _ := rfl

@[simp] theorem inversePostcompose_hom (K : C ⥤ D)
    (F : SingleObj (M G H) ⥤ C) :
    ((functorToRepresentationPostcomposeIso G H K).hom.app F).hom = 𝟙 _ := rfl

#print axioms representationSingleObjEquivalence
#print axioms representationToFunctorPostcomposeIso
#print axioms functorToRepresentationPostcomposeIso

end ConstructionTargets.FreeProductRepresentationSingleObjEquivalence
