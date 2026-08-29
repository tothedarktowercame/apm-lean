import ConstructionTargets.TwiceSpiralPushoutSingleObjEquivalence

/-!
# Representability candidates for the twice-spiral groupoid

Fixed-target mapping-category equivalences do not by themselves give an
equivalence of their source categories.  This file defines the two candidate
source functors by evaluating the compiled mapping equivalence on identity
functors, and proves the target-change comparison for its final algebraic
layer.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralRepresentabilityCandidates

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
open ConstructionTargets.TwiceSpiralConnectorLegCompatibility
open ConstructionTargets.TwiceSpiralFundamentalGroupPushout
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates
open ConstructionTargets.TwiceSpiralPushoutRepresentations
open ConstructionTargets.TwiceSpiralPushoutSingleObjEquivalence

variable {h : BoundaryTorus ≃ₜ BoundaryTorus} {d : ℤ}
variable (B : PointedCoordinateBases h d) (K : LegCompatibleConnectorSystems B)

/-- The candidate functor from the gluing fundamental groupoid to the
single-object twice-spiral pushout category.  It is the inverse image of the
identity functor at target `SingleObj (TwiceSpiralPushout d)`. -/
def gluingToPushoutCandidate :
    FundamentalGroupoid (Gluing h) ⥤ SingleObj (TwiceSpiralPushout d) :=
  (gluingFundamentalGroupoidSingleObjMappingEquivalence
    (SingleObj (TwiceSpiralPushout d)) B K).inverse.obj
      (𝟭 (SingleObj (TwiceSpiralPushout d)))

/-- The candidate functor in the reverse direction.  It is the forward image
of the identity functor at target `FundamentalGroupoid (Gluing h)`. -/
def pushoutToGluingCandidate :
    SingleObj (TwiceSpiralPushout d) ⥤ FundamentalGroupoid (Gluing h) :=
  (gluingFundamentalGroupoidSingleObjMappingEquivalence
    (FundamentalGroupoid (Gluing h)) B K).functor.obj
      (𝟭 (FundamentalGroupoid (Gluing h)))

variable {C D : Type} [Groupoid C] [Groupoid D]

/-- Postcompose a pushout representation by a functor between target
groupoids. -/
def postcomposeRepresentationObj (H : C ⥤ D)
    (R : PushoutRepresentation (d := d) C) : PushoutRepresentation (d := d) D where
  target := H.obj R.target
  action := {
    toFun := fun g => H.map (R.action g)
    map_one' := by
      rw [R.action.map_one]
      exact H.map_id _
    map_mul' := by
      intro x y
      rw [R.action.map_mul]
      change H.map (R.action y ≫ R.action x) =
        H.map (R.action y) ≫ H.map (R.action x)
      exact H.map_comp _ _ }

def postcomposeRepresentationMap (H : C ⥤ D)
    {R Q : PushoutRepresentation (d := d) C} (f : R ⟶ Q) :
    postcomposeRepresentationObj H R ⟶ postcomposeRepresentationObj H Q where
  hom := by
    change H.obj R.target ⟶ H.obj Q.target
    exact H.map f.hom
  intertwines g := by
    change H.map (R.action g) ≫ H.map f.hom =
      H.map f.hom ≫ H.map (Q.action g)
    rw [← H.map_comp, ← H.map_comp, f.intertwines]

/-- Target change on pushout representations. -/
def postcomposeRepresentationFunctor (H : C ⥤ D) :
    PushoutRepresentation (d := d) C ⥤ PushoutRepresentation (d := d) D where
  obj := postcomposeRepresentationObj H
  map := postcomposeRepresentationMap H
  map_id R := by
    apply PushoutRepresentationHom.ext
    change H.map (𝟙 R.target) = 𝟙 (H.obj R.target)
    exact H.map_id _
  map_comp f g := by
    apply PushoutRepresentationHom.ext
    change H.map (f.hom ≫ g.hom) = H.map f.hom ≫ H.map g.hom
    exact H.map_comp _ _

/-- At the final algebraic layer, converting a representation to a
single-object functor commutes with postcomposition.  Components are literal
identity arrows; no source-category equivalence is inferred here. -/
def representationToFunctorPostcomposeIso (H : C ⥤ D) :
    postcomposeRepresentationFunctor (d := d) H ⋙ representationToFunctor D ≅
      representationToFunctor C ⋙
        (Functor.whiskeringRight (SingleObj (TwiceSpiralPushout d)) C D).obj H :=
  NatIso.ofComponents (fun (R : PushoutRepresentation (d := d) C) =>
    NatIso.ofComponents
      (fun X : SingleObj (TwiceSpiralPushout d) => by cases X; exact Iso.refl _)
      (by
      intro X Y f
      cases X
      cases Y
      change H.map (R.action f) ≫ 𝟙 _ = 𝟙 _ ≫ H.map (R.action f)
      simp)) (by
    intro R Q f
    ext X
    cases X
    change H.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ H.map f.hom
    simp)

@[simp] theorem representationToFunctorPostcomposeIso_hom_app_star
    (H : C ⥤ D) (R : PushoutRepresentation (d := d) C) :
    ((representationToFunctorPostcomposeIso (d := d) H).hom.app R).app
      (SingleObj.star _) = 𝟙 _ := rfl

#print axioms gluingToPushoutCandidate
#print axioms pushoutToGluingCandidate
#print axioms postcomposeRepresentationFunctor
#print axioms representationToFunctorPostcomposeIso

end ConstructionTargets.TwiceSpiralRepresentabilityCandidates
