import ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

/-!
# Functor-category transport for the twice-spiral collar span

This file packages the three functor-category equivalences induced by the
collar deformation equivalences.  The subsequent pseudococone transport must
insert their unit isomorphisms around the overlap glue; those isomorphisms are
not definitionally identities.
-/

open CategoryTheory
open scoped FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralPseudococoneTransport

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralFundamentalGroupoidOpenCover
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

variable (h : BoundaryTorus ≃ₜ BoundaryTorus)
variable (C : Type) [Category C]

/-- Precomposition with the inverse left-piece equivalence transports
functors on the collared left piece to solid-torus functors. -/
def leftFunctorCategoryEquivalence :
    (FundamentalGroupoid (U h) ⥤ C) ≌
      (FundamentalGroupoid SolidTorus ⥤ C) :=
  (leftFundamentalGroupoidEquivalence h).congrLeft

/-- Precomposition with the inverse right-piece equivalence transports
functors on the collared right piece to solid-torus functors. -/
def rightFunctorCategoryEquivalence :
    (FundamentalGroupoid (V h) ⥤ C) ≌
      (FundamentalGroupoid SolidTorus ⥤ C) :=
  (rightFundamentalGroupoidEquivalence h).congrLeft

/-- Precomposition with the inverse overlap equivalence transports functors
on the collared intersection to boundary-torus functors. -/
def overlapFunctorCategoryEquivalence :
    (FundamentalGroupoid (U h ∩ V h : Set (Gluing h)) ⥤ C) ≌
      (FundamentalGroupoid BoundaryTorus ⥤ C) :=
  (overlapFundamentalGroupoidEquivalence h).congrLeft

@[simp] theorem leftFunctorCategoryEquivalence_obj
    (F : FundamentalGroupoid (U h) ⥤ C) :
    (leftFunctorCategoryEquivalence h C).functor.obj F =
      (leftFundamentalGroupoidEquivalence h).inverse ⋙ F := rfl

@[simp] theorem rightFunctorCategoryEquivalence_obj
    (F : FundamentalGroupoid (V h) ⥤ C) :
    (rightFunctorCategoryEquivalence h C).functor.obj F =
      (rightFundamentalGroupoidEquivalence h).inverse ⋙ F := rfl

@[simp] theorem overlapFunctorCategoryEquivalence_obj
    (F : FundamentalGroupoid (U h ∩ V h : Set (Gluing h)) ⥤ C) :
    (overlapFunctorCategoryEquivalence h C).functor.obj F =
      (overlapFundamentalGroupoidEquivalence h).inverse ⋙ F := rfl

/-- The exact left span comparison before cancelling the piece equivalence's
unit.  This is the orientation used to transport actual overlap glue. -/
theorem left_span_coordinate_equation :
    (overlapFundamentalGroupoidEquivalence h).inverse ⋙
        FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙
        (leftFundamentalGroupoidEquivalence h).functor =
      coordinateLeftLeg :=
  actual_left_leg_in_coordinates h

/-- The exact right span comparison before cancelling the piece equivalence's
unit. -/
theorem right_span_coordinate_equation :
    (overlapFundamentalGroupoidEquivalence h).inverse ⋙
        FundamentalGroupoid.map (intersectionToRightOpen h) ⋙
        (rightFundamentalGroupoidEquivalence h).functor =
      coordinateRightLeg h :=
  actual_right_leg_in_coordinates h

#print axioms leftFunctorCategoryEquivalence
#print axioms rightFunctorCategoryEquivalence
#print axioms overlapFunctorCategoryEquivalence
#print axioms leftFunctorCategoryEquivalence_obj
#print axioms rightFunctorCategoryEquivalence_obj
#print axioms overlapFunctorCategoryEquivalence_obj
#print axioms left_span_coordinate_equation
#print axioms right_span_coordinate_equation

end ConstructionTargets.TwiceSpiralPseudococoneTransport
