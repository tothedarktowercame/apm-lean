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
open ConstructionTargets.TwoOpenFundamentalGroupoidSpan

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

/-- Coordinate-left restriction agrees with transporting the actual left
restriction through the overlap equivalence.  The final comparison is the
inverse unit of the left groupoid equivalence, not a definitional equality. -/
def leftSpanComparison
    (L : FundamentalGroupoid (U h) ⥤ C) :
    coordinateLeftLeg ⋙ (leftFunctorCategoryEquivalence h C).functor.obj L ≅
      (overlapFundamentalGroupoidEquivalence h).inverse ⋙
        FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙ L := by
  let e := leftFundamentalGroupoidEquivalence h
  let K := (overlapFundamentalGroupoidEquivalence h).inverse ⋙
    FundamentalGroupoid.map (intersectionToLeftOpen h)
  let q : coordinateLeftLeg ⋙ e.inverse = K ⋙ e.functor ⋙ e.inverse :=
    congrArg (fun J => J ⋙ e.inverse) (left_span_coordinate_equation h).symm
  exact (Functor.isoWhiskerRight (eqToIso q) L).trans
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft K e.unitIso.symm) L)

/-- Right-hand analogue of `leftSpanComparison`. -/
def rightSpanComparison
    (R : FundamentalGroupoid (V h) ⥤ C) :
    coordinateRightLeg h ⋙ (rightFunctorCategoryEquivalence h C).functor.obj R ≅
      (overlapFundamentalGroupoidEquivalence h).inverse ⋙
        FundamentalGroupoid.map (intersectionToRightOpen h) ⋙ R := by
  let e := rightFundamentalGroupoidEquivalence h
  let K := (overlapFundamentalGroupoidEquivalence h).inverse ⋙
    FundamentalGroupoid.map (intersectionToRightOpen h)
  let q : coordinateRightLeg h ⋙ e.inverse = K ⋙ e.functor ⋙ e.inverse :=
    congrArg (fun J => J ⋙ e.inverse) (right_span_coordinate_equation h).symm
  exact (Functor.isoWhiskerRight (eqToIso q) R).trans
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft K e.unitIso.symm) R)

/-- Whiskering the actual overlap comparison through the inverse overlap
equivalence gives the middle 2-cell used by coordinate transport. -/
def transportedOverlapGlue
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    (overlapFundamentalGroupoidEquivalence h).inverse ⋙
        FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙ P.left ≅
      (overlapFundamentalGroupoidEquivalence h).inverse ⋙
        FundamentalGroupoid.map (intersectionToRightOpen h) ⋙ P.right :=
  Functor.isoWhiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse P.glue

/-- Forward transport of an actual collar-cover pseudococone into the
solid-torus/boundary-torus coordinates. -/
def actualPseudoCoconeToCoordinateObj
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    CoordinatePseudoCocone h C where
  left := (leftFunctorCategoryEquivalence h C).functor.obj P.left
  right := (rightFunctorCategoryEquivalence h C).functor.obj P.right
  glue := (leftSpanComparison h C P.left).trans
    ((transportedOverlapGlue h C P).trans (rightSpanComparison h C P.right).symm)

theorem leftSpanComparison_naturality
    {L M : FundamentalGroupoid (U h) ⥤ C} (tau : L ⟶ M) :
    (leftSpanComparison h C L).hom ≫
        Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).inverse ⋙
            FundamentalGroupoid.map (intersectionToLeftOpen h)) tau =
      Functor.whiskerLeft coordinateLeftLeg
          ((leftFunctorCategoryEquivalence h C).functor.map tau) ≫
        (leftSpanComparison h C M).hom := by
  ext z
  simp [leftSpanComparison, Category.assoc]
  rfl

theorem rightSpanComparison_naturality
    {L M : FundamentalGroupoid (V h) ⥤ C} (tau : L ⟶ M) :
    (rightSpanComparison h C L).hom ≫
        Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).inverse ⋙
            FundamentalGroupoid.map (intersectionToRightOpen h)) tau =
      Functor.whiskerLeft (coordinateRightLeg h)
          ((rightFunctorCategoryEquivalence h C).functor.map tau) ≫
        (rightSpanComparison h C M).hom := by
  ext z
  simp [rightSpanComparison, Category.assoc]
  rfl

theorem transportedOverlapGlue_naturality
    {P Q : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)}
    (tau : P ⟶ Q) :
    (transportedOverlapGlue h C P).hom ≫
        Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).inverse ⋙
            FundamentalGroupoid.map (intersectionToRightOpen h)) tau.right =
      Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).inverse ⋙
            FundamentalGroupoid.map (intersectionToLeftOpen h)) tau.left ≫
        (transportedOverlapGlue h C Q).hom := by
  simpa [transportedOverlapGlue, Functor.whiskerLeft_comp] using
    congrArg (Functor.whiskerLeft
      (overlapFundamentalGroupoidEquivalence h).inverse) tau.glue_naturality

theorem rightSpanComparison_inv_naturality
    {L M : FundamentalGroupoid (V h) ⥤ C} (tau : L ⟶ M) :
    (rightSpanComparison h C L).inv ≫
        Functor.whiskerLeft (coordinateRightLeg h)
          ((rightFunctorCategoryEquivalence h C).functor.map tau) =
      Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).inverse ⋙
            FundamentalGroupoid.map (intersectionToRightOpen h)) tau ≫
        (rightSpanComparison h C M).inv := by
  exact (ConstructionTargets.TwoOpenPseudoCoconeStrictification.iso_square_inverse
    (rightSpanComparison h C L) (rightSpanComparison h C M)
    (Functor.whiskerLeft (coordinateRightLeg h)
      ((rightFunctorCategoryEquivalence h C).functor.map tau))
    (Functor.whiskerLeft
      ((overlapFundamentalGroupoidEquivalence h).inverse ⋙
        FundamentalGroupoid.map (intersectionToRightOpen h)) tau)
    (rightSpanComparison_naturality h C tau).symm).symm

theorem three_square_pasting
    {A B D E A' B' D' E' : C}
    (l : A ⟶ B) (m : B ⟶ D) (r : D ⟶ E)
    (l' : A' ⟶ B') (m' : B' ⟶ D') (r' : D' ⟶ E')
    (a : B ⟶ B') (b : D ⟶ D') (x : A ⟶ A') (y : E ⟶ E')
    (hl : l ≫ a = x ≫ l') (hm : m ≫ b = a ≫ m')
    (hr : r ≫ y = b ≫ r') :
    (l ≫ m ≫ r) ≫ y = x ≫ (l' ≫ m' ≫ r') := by
  simp only [Category.assoc]
  rw [hr, ← Category.assoc m, hm, Category.assoc,
    ← Category.assoc l, hl]
  exact Category.assoc x l' (m' ≫ r')

/-- A morphism of actual collar pseudococones transports to a morphism of
coordinate pseudococones. -/
def actualPseudoCoconeToCoordinateMap
    {P Q : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)}
    (tau : P ⟶ Q) :
    actualPseudoCoconeToCoordinateObj h C P ⟶
      actualPseudoCoconeToCoordinateObj h C Q where
  left := (leftFunctorCategoryEquivalence h C).functor.map tau.left
  right := (rightFunctorCategoryEquivalence h C).functor.map tau.right
  glue_naturality := by
    dsimp [actualPseudoCoconeToCoordinateObj]
    exact three_square_pasting
      (C := FundamentalGroupoid BoundaryTorus ⥤ C)
      (l := (leftSpanComparison h C P.left).hom)
      (m := (transportedOverlapGlue h C P).hom)
      (r := (rightSpanComparison h C P.right).inv)
      (l' := (leftSpanComparison h C Q.left).hom)
      (m' := (transportedOverlapGlue h C Q).hom)
      (r' := (rightSpanComparison h C Q.right).inv)
      (a := Functor.whiskerLeft
        ((overlapFundamentalGroupoidEquivalence h).inverse ⋙
          FundamentalGroupoid.map (intersectionToLeftOpen h)) tau.left)
      (b := Functor.whiskerLeft
        ((overlapFundamentalGroupoidEquivalence h).inverse ⋙
          FundamentalGroupoid.map (intersectionToRightOpen h)) tau.right)
      (x := Functor.whiskerLeft coordinateLeftLeg
        ((leftFunctorCategoryEquivalence h C).functor.map tau.left))
      (y := Functor.whiskerLeft (coordinateRightLeg h)
        ((rightFunctorCategoryEquivalence h C).functor.map tau.right))
      (leftSpanComparison_naturality h C tau.left)
      (transportedOverlapGlue_naturality h C tau)
      (rightSpanComparison_inv_naturality h C tau.right)

/-- Forward functor transporting actual collar pseudococones into the
solid-torus/boundary-torus coordinate span. -/
def actualPseudoCoconeToCoordinateFunctor :
    PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C) ⥤
      CoordinatePseudoCocone h C where
  obj := actualPseudoCoconeToCoordinateObj h C
  map := actualPseudoCoconeToCoordinateMap h C
  map_id P := by
    apply CoordinatePseudoCoconeHom.ext
    · exact (leftFunctorCategoryEquivalence h C).functor.map_id P.left
    · exact (rightFunctorCategoryEquivalence h C).functor.map_id P.right
  map_comp f g := by
    apply CoordinatePseudoCoconeHom.ext
    · exact (leftFunctorCategoryEquivalence h C).functor.map_comp f.left g.left
    · exact (rightFunctorCategoryEquivalence h C).functor.map_comp f.right g.right

#print axioms leftFunctorCategoryEquivalence
#print axioms rightFunctorCategoryEquivalence
#print axioms overlapFunctorCategoryEquivalence
#print axioms leftFunctorCategoryEquivalence_obj
#print axioms rightFunctorCategoryEquivalence_obj
#print axioms overlapFunctorCategoryEquivalence_obj
#print axioms left_span_coordinate_equation
#print axioms right_span_coordinate_equation
#print axioms leftSpanComparison
#print axioms rightSpanComparison
#print axioms transportedOverlapGlue
#print axioms actualPseudoCoconeToCoordinateObj
#print axioms leftSpanComparison_naturality
#print axioms rightSpanComparison_naturality
#print axioms transportedOverlapGlue_naturality
#print axioms rightSpanComparison_inv_naturality
#print axioms three_square_pasting
#print axioms actualPseudoCoconeToCoordinateMap
#print axioms actualPseudoCoconeToCoordinateFunctor

end ConstructionTargets.TwiceSpiralPseudococoneTransport
