import ConstructionTargets.TwiceSpiralPushoutRepresentationRoundTrip
import Mathlib.CategoryTheory.SingleObj

open CategoryTheory
noncomputable section

namespace ConstructionTargets.TwiceSpiralPushoutSingleObjEquivalence

open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralPushoutRepresentations
open ConstructionTargets.TwiceSpiralPushoutRepresentationRoundTrip

variable {d : ℤ} (C : Type) [Groupoid C]

def representationToFunctorObj (R : PushoutRepresentation (d := d) C) :
    SingleObj (TwiceSpiralPushout d) ⥤ C := SingleObj.functor R.action

def representationToFunctorMap {R S : PushoutRepresentation (d := d) C}
    (f : R ⟶ S) : representationToFunctorObj C R ⟶ representationToFunctorObj C S :=
  SingleObj.natTrans f.hom f.intertwines

def representationToFunctor :
    PushoutRepresentation (d := d) C ⥤
      (SingleObj (TwiceSpiralPushout d) ⥤ C) where
  obj := representationToFunctorObj C
  map := representationToFunctorMap C
  map_id _ := by ext X; cases X; rfl
  map_comp _ _ := by ext X; cases X; rfl

/-- The map of a single-object functor, viewed with the multiplication
orientation of `End`. -/
def functorAction (F : SingleObj (TwiceSpiralPushout d) ⥤ C) :
    TwiceSpiralPushout d →* End (F.obj (SingleObj.star _)) where
  toFun g := F.map g
  map_one' := F.map_id _
  map_mul' x y := by
    rw [End.mul_def]
    rw [← F.map_comp]
    rw [SingleObj.comp_as_mul]

def functorToRepresentationObj (F : SingleObj (TwiceSpiralPushout d) ⥤ C) :
    PushoutRepresentation (d := d) C where
  target := F.obj (SingleObj.star _)
  action := functorAction C F

def functorToRepresentationMap
    {F G : SingleObj (TwiceSpiralPushout d) ⥤ C} (τ : F ⟶ G) :
    functorToRepresentationObj C F ⟶ functorToRepresentationObj C G where
  hom := τ.app (SingleObj.star _)
  intertwines g := τ.naturality g

def functorToRepresentation :
    (SingleObj (TwiceSpiralPushout d) ⥤ C) ⥤
      PushoutRepresentation (d := d) C where
  obj := functorToRepresentationObj C
  map := functorToRepresentationMap C
  map_id _ := by apply PushoutRepresentationHom.ext; rfl
  map_comp _ _ := by apply PushoutRepresentationHom.ext; rfl

def representationRoundTripIso (R : PushoutRepresentation (d := d) C) :
    ((representationToFunctor C) ⋙ (functorToRepresentation C)).obj R ≅ R where
  hom := ⟨𝟙 _, by
    intro g
    change R.action g ≫ 𝟙 _ = 𝟙 _ ≫ R.action g
    simp⟩
  inv := ⟨𝟙 _, by
    intro g
    change R.action g ≫ 𝟙 _ = 𝟙 _ ≫ R.action g
    simp⟩
  hom_inv_id := by
    apply PushoutRepresentationHom.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply PushoutRepresentationHom.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- Every object of `SingleObj` is its unique star; after eliminating that
index, the reconstructed functor agrees with the original functor. -/
def functorRoundTripIso (F : SingleObj (TwiceSpiralPushout d) ⥤ C) :
    ((functorToRepresentation C) ⋙ (representationToFunctor C)).obj F ≅ F :=
  NatIso.ofComponents (fun X => by cases X; exact Iso.refl _) (by
    intro X Y f
    cases X
    cases Y
    change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    simp)

theorem representationRoundTripIso_naturality
    {R S : PushoutRepresentation (d := d) C} (f : R ⟶ S) :
    ((representationToFunctor C) ⋙ (functorToRepresentation C)).map f ≫
        (representationRoundTripIso C S).hom =
      (representationRoundTripIso C R).hom ≫ f := by
  apply PushoutRepresentationHom.ext
  change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
  simp

theorem functorRoundTripIso_naturality
    {F G : SingleObj (TwiceSpiralPushout d) ⥤ C} (τ : F ⟶ G) :
    ((functorToRepresentation C) ⋙ (representationToFunctor C)).map τ ≫
        (functorRoundTripIso C G).hom =
      (functorRoundTripIso C F).hom ≫ τ := by
  ext X
  cases X
  change τ.app (SingleObj.star _) ≫ 𝟙 _ = 𝟙 _ ≫ τ.app (SingleObj.star _)
  simp

def representationRoundTripNatIso :
    representationToFunctor C ⋙ functorToRepresentation C ≅
      𝟭 (PushoutRepresentation (d := d) C) :=
  NatIso.ofComponents (representationRoundTripIso C) (by
    intro R S f; exact representationRoundTripIso_naturality C f)

def functorRoundTripNatIso :
    functorToRepresentation C ⋙ representationToFunctor C ≅
      𝟭 (SingleObj (TwiceSpiralPushout d) ⥤ C) :=
  NatIso.ofComponents (functorRoundTripIso C) (by
    intro F G τ; exact functorRoundTripIso_naturality C τ)

theorem representation_functor_triangle (R : PushoutRepresentation (d := d) C) :
    (representationToFunctor C).map
          ((representationRoundTripNatIso C).symm.hom.app R) ≫
        (functorRoundTripNatIso C).hom.app
          ((representationToFunctor C).obj R) =
      𝟙 ((representationToFunctor C).obj R) := by
  ext X
  cases X
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp

def pushoutRepresentationSingleObjEquivalence :
    PushoutRepresentation (d := d) C ≌
      (SingleObj (TwiceSpiralPushout d) ⥤ C) :=
  CategoryTheory.Equivalence.mk'
    (representationToFunctor C) (functorToRepresentation C)
    (representationRoundTripNatIso C).symm (functorRoundTripNatIso C)
    (representation_functor_triangle C)

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable {h : BoundaryTorus ≃ₜ BoundaryTorus}

def gluingFundamentalGroupoidSingleObjMappingEquivalence
    (B : PointedCoordinateBases h d) (K : LegCompatibleConnectorSystems B) :
    Functor (FundamentalGroupoid (Gluing h)) C ≌
      (SingleObj (TwiceSpiralPushout d) ⥤ C) :=
  (gluingFundamentalGroupoidPushoutRepresentationEquivalence C B K).trans
    (pushoutRepresentationSingleObjEquivalence C)

#print axioms functorAction
#print axioms representationToFunctor
#print axioms functorToRepresentation
#print axioms pushoutRepresentationSingleObjEquivalence
#print axioms gluingFundamentalGroupoidSingleObjMappingEquivalence

end ConstructionTargets.TwiceSpiralPushoutSingleObjEquivalence
