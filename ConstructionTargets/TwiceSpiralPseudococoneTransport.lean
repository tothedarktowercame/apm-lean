import ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates
import ConstructionTargets.EquivalenceSpanRoundTrip

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

/-- Left whiskering preserves a parenthesized composite of three natural
transformations, with the association exposed for subsequent block rewrites. -/
theorem whiskerLeft_three_comp
    {A B : Type} [Category A] [Category B]
    (F : Functor A B) {G₀ G₁ G₂ G₃ : Functor B C}
    (a : G₀ ⟶ G₁) (b : G₁ ⟶ G₂) (c : G₂ ⟶ G₃) :
    Functor.whiskerLeft F (a ≫ b ≫ c) =
      Functor.whiskerLeft F a ≫ Functor.whiskerLeft F b ≫
        Functor.whiskerLeft F c := by
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]

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

/-- After precomposing the coordinate left leg by the forward overlap
equivalence, its comparison with the actual left leg uses the inverse unit of
the overlap equivalence. -/
def reverseLeftSpanComparison
    (L : FundamentalGroupoid SolidTorus ⥤ C) :
    (overlapFundamentalGroupoidEquivalence h).functor ⋙
        coordinateLeftLeg ⋙ L ≅
      FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙
        (leftFundamentalGroupoidEquivalence h).functor ⋙ L := by
  let eO := overlapFundamentalGroupoidEquivalence h
  let K := FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙
    (leftFundamentalGroupoidEquivalence h).functor
  let q : eO.functor ⋙ coordinateLeftLeg =
      eO.functor ⋙ eO.inverse ⋙ K :=
    congrArg (fun J => eO.functor ⋙ J) (left_span_coordinate_equation h).symm
  exact (Functor.isoWhiskerRight (eqToIso q) L).trans
    (Functor.isoWhiskerRight (eO.funInvIdAssoc K) L)

/-- Right-hand analogue of `reverseLeftSpanComparison`. -/
def reverseRightSpanComparison
    (R : FundamentalGroupoid SolidTorus ⥤ C) :
    (overlapFundamentalGroupoidEquivalence h).functor ⋙
        coordinateRightLeg h ⋙ R ≅
      FundamentalGroupoid.map (intersectionToRightOpen h) ⋙
        (rightFundamentalGroupoidEquivalence h).functor ⋙ R := by
  let eO := overlapFundamentalGroupoidEquivalence h
  let K := FundamentalGroupoid.map (intersectionToRightOpen h) ⋙
    (rightFundamentalGroupoidEquivalence h).functor
  let q : eO.functor ⋙ coordinateRightLeg h =
      eO.functor ⋙ eO.inverse ⋙ K :=
    congrArg (fun J => eO.functor ⋙ J) (right_span_coordinate_equation h).symm
  exact (Functor.isoWhiskerRight (eqToIso q) R).trans
    (Functor.isoWhiskerRight (eO.funInvIdAssoc K) R)

/-- Coordinate overlap glue whiskered through the forward overlap
equivalence. -/
def reverseTransportedOverlapGlue (P : CoordinatePseudoCocone h C) :
    (overlapFundamentalGroupoidEquivalence h).functor ⋙
        coordinateLeftLeg ⋙ P.left ≅
      (overlapFundamentalGroupoidEquivalence h).functor ⋙
        coordinateRightLeg h ⋙ P.right :=
  Functor.isoWhiskerLeft (overlapFundamentalGroupoidEquivalence h).functor P.glue

/-- Reverse object transport from coordinate pseudococones to the actual
collar-cover span. -/
def coordinateToActualPseudoCoconeObj (P : CoordinatePseudoCocone h C) :
    PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C) where
  left := (leftFunctorCategoryEquivalence h C).inverse.obj P.left
  right := (rightFunctorCategoryEquivalence h C).inverse.obj P.right
  glue := (reverseLeftSpanComparison h C P.left).symm.trans
    ((reverseTransportedOverlapGlue h C P).trans
      (reverseRightSpanComparison h C P.right))

theorem reverseLeftSpanComparison_naturality
    {L M : FundamentalGroupoid SolidTorus ⥤ C} (tau : L ⟶ M) :
    (reverseLeftSpanComparison h C L).hom ≫
        Functor.whiskerLeft
          (FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙
            (leftFundamentalGroupoidEquivalence h).functor) tau =
      Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).functor ⋙
            coordinateLeftLeg) tau ≫
        (reverseLeftSpanComparison h C M).hom := by
  ext z
  simp [reverseLeftSpanComparison, Category.assoc]

theorem reverseRightSpanComparison_naturality
    {L M : FundamentalGroupoid SolidTorus ⥤ C} (tau : L ⟶ M) :
    (reverseRightSpanComparison h C L).hom ≫
        Functor.whiskerLeft
          (FundamentalGroupoid.map (intersectionToRightOpen h) ⋙
            (rightFundamentalGroupoidEquivalence h).functor) tau =
      Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).functor ⋙
            coordinateRightLeg h) tau ≫
        (reverseRightSpanComparison h C M).hom := by
  ext z
  simp [reverseRightSpanComparison, Category.assoc]

theorem reverseLeftSpanComparison_inv_naturality
    {L M : FundamentalGroupoid SolidTorus ⥤ C} (tau : L ⟶ M) :
    (reverseLeftSpanComparison h C L).inv ≫
        Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).functor ⋙
            coordinateLeftLeg) tau =
      Functor.whiskerLeft
          (FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙
            (leftFundamentalGroupoidEquivalence h).functor) tau ≫
        (reverseLeftSpanComparison h C M).inv := by
  exact (ConstructionTargets.TwoOpenPseudoCoconeStrictification.iso_square_inverse
    (reverseLeftSpanComparison h C L) (reverseLeftSpanComparison h C M)
    (Functor.whiskerLeft
      ((overlapFundamentalGroupoidEquivalence h).functor ⋙ coordinateLeftLeg) tau)
    (Functor.whiskerLeft
      (FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙
        (leftFundamentalGroupoidEquivalence h).functor) tau)
    (reverseLeftSpanComparison_naturality h C tau).symm).symm

theorem reverseTransportedOverlapGlue_naturality
    {P Q : CoordinatePseudoCocone h C} (tau : P ⟶ Q) :
    (reverseTransportedOverlapGlue h C P).hom ≫
        Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).functor ⋙
            coordinateRightLeg h) tau.right =
      Functor.whiskerLeft
          ((overlapFundamentalGroupoidEquivalence h).functor ⋙
            coordinateLeftLeg) tau.left ≫
        (reverseTransportedOverlapGlue h C Q).hom := by
  ext z
  have hz := congrArg (fun k => k.app
    ((overlapFundamentalGroupoidEquivalence h).functor.obj z))
    tau.glue_naturality
  simpa [reverseTransportedOverlapGlue, Category.assoc] using hz

/-- Reverse transport of coordinate pseudococone morphisms. -/
def coordinateToActualPseudoCoconeMap
    {P Q : CoordinatePseudoCocone h C} (tau : P ⟶ Q) :
    coordinateToActualPseudoCoconeObj h C P ⟶
      coordinateToActualPseudoCoconeObj h C Q where
  left := (leftFunctorCategoryEquivalence h C).inverse.map tau.left
  right := (rightFunctorCategoryEquivalence h C).inverse.map tau.right
  glue_naturality := by
    dsimp [coordinateToActualPseudoCoconeObj]
    exact three_square_pasting
      (C := FundamentalGroupoid (U h ∩ V h : Set (Gluing h)) ⥤ C)
      (l := (reverseLeftSpanComparison h C P.left).inv)
      (m := (reverseTransportedOverlapGlue h C P).hom)
      (r := (reverseRightSpanComparison h C P.right).hom)
      (l' := (reverseLeftSpanComparison h C Q.left).inv)
      (m' := (reverseTransportedOverlapGlue h C Q).hom)
      (r' := (reverseRightSpanComparison h C Q.right).hom)
      (a := Functor.whiskerLeft
        ((overlapFundamentalGroupoidEquivalence h).functor ⋙
          coordinateLeftLeg) tau.left)
      (b := Functor.whiskerLeft
        ((overlapFundamentalGroupoidEquivalence h).functor ⋙
          coordinateRightLeg h) tau.right)
      (x := Functor.whiskerLeft
        (FundamentalGroupoid.map (intersectionToLeftOpen h))
        ((leftFunctorCategoryEquivalence h C).inverse.map tau.left))
      (y := Functor.whiskerLeft
        (FundamentalGroupoid.map (intersectionToRightOpen h))
        ((rightFunctorCategoryEquivalence h C).inverse.map tau.right))
      (reverseLeftSpanComparison_inv_naturality h C tau.left)
      (reverseTransportedOverlapGlue_naturality h C tau)
      (reverseRightSpanComparison_naturality h C tau.right)

/-- Reverse functor from coordinate pseudococones to actual collar-cover
pseudococones. -/
def coordinateToActualPseudoCoconeFunctor :
    CoordinatePseudoCocone h C ⥤
      PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C) where
  obj := coordinateToActualPseudoCoconeObj h C
  map := coordinateToActualPseudoCoconeMap h C
  map_id P := by
    apply PseudoFunctorCoconeHom.ext
    · exact (leftFunctorCategoryEquivalence h C).inverse.map_id P.left
    · exact (rightFunctorCategoryEquivalence h C).inverse.map_id P.right
  map_comp f g := by
    apply PseudoFunctorCoconeHom.ext
    · exact (leftFunctorCategoryEquivalence h C).inverse.map_comp f.left g.left
    · exact (rightFunctorCategoryEquivalence h C).inverse.map_comp f.right g.right

/-- Left component of the actual-pseudococone round-trip unit. -/
def actualLeftRoundTripIso
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    P.left ≅ (leftFunctorCategoryEquivalence h C).inverse.obj
      ((leftFunctorCategoryEquivalence h C).functor.obj P.left) :=
  (leftFunctorCategoryEquivalence h C).unitIso.app P.left

/-- Right component of the actual-pseudococone round-trip unit. -/
def actualRightRoundTripIso
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    P.right ≅ (rightFunctorCategoryEquivalence h C).inverse.obj
      ((rightFunctorCategoryEquivalence h C).functor.obj P.right) :=
  (rightFunctorCategoryEquivalence h C).unitIso.app P.right

/-- Left component of the coordinate-pseudococone round-trip counit. -/
def coordinateLeftRoundTripIso (P : CoordinatePseudoCocone h C) :
    (leftFunctorCategoryEquivalence h C).functor.obj
        ((leftFunctorCategoryEquivalence h C).inverse.obj P.left) ≅ P.left :=
  (leftFunctorCategoryEquivalence h C).counitIso.app P.left

/-- Right component of the coordinate-pseudococone round-trip counit. -/
def coordinateRightRoundTripIso (P : CoordinatePseudoCocone h C) :
    (rightFunctorCategoryEquivalence h C).functor.obj
        ((rightFunctorCategoryEquivalence h C).inverse.obj P.right) ≅ P.right :=
  (rightFunctorCategoryEquivalence h C).counitIso.app P.right

theorem actualLeftRoundTripIso_naturality
    {P Q : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)}
    (tau : P ⟶ Q) :
    tau.left ≫ (actualLeftRoundTripIso h C Q).hom =
      (actualLeftRoundTripIso h C P).hom ≫
        (leftFunctorCategoryEquivalence h C).inverse.map
          ((leftFunctorCategoryEquivalence h C).functor.map tau.left) :=
  (leftFunctorCategoryEquivalence h C).unitIso.hom.naturality tau.left

theorem actualRightRoundTripIso_naturality
    {P Q : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)}
    (tau : P ⟶ Q) :
    tau.right ≫ (actualRightRoundTripIso h C Q).hom =
      (actualRightRoundTripIso h C P).hom ≫
        (rightFunctorCategoryEquivalence h C).inverse.map
          ((rightFunctorCategoryEquivalence h C).functor.map tau.right) :=
  (rightFunctorCategoryEquivalence h C).unitIso.hom.naturality tau.right

theorem coordinateLeftRoundTripIso_naturality
    {P Q : CoordinatePseudoCocone h C} (tau : P ⟶ Q) :
    (leftFunctorCategoryEquivalence h C).functor.map
          ((leftFunctorCategoryEquivalence h C).inverse.map tau.left) ≫
        (coordinateLeftRoundTripIso h C Q).hom =
      (coordinateLeftRoundTripIso h C P).hom ≫ tau.left :=
  (leftFunctorCategoryEquivalence h C).counitIso.hom.naturality tau.left

theorem coordinateRightRoundTripIso_naturality
    {P Q : CoordinatePseudoCocone h C} (tau : P ⟶ Q) :
    (rightFunctorCategoryEquivalence h C).functor.map
          ((rightFunctorCategoryEquivalence h C).inverse.map tau.right) ≫
        (coordinateRightRoundTripIso h C Q).hom =
      (coordinateRightRoundTripIso h C P).hom ≫ tau.right :=
  (rightFunctorCategoryEquivalence h C).counitIso.hom.naturality tau.right

/-- Naturality of the actual overlap glue at the unit arrow of the overlap
groupoid equivalence.  Both induced inclusion maps remain explicit. -/
theorem actualGlue_overlapUnit_naturality
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C))
    (z : FundamentalGroupoid (U h ∩ V h : Set (Gluing h))) :
    P.left.map ((FundamentalGroupoid.map (intersectionToLeftOpen h)).map
        ((overlapFundamentalGroupoidEquivalence h).unitIso.hom.app z)) ≫
      P.glue.hom.app
        ((overlapFundamentalGroupoidEquivalence h).inverse.obj
          ((overlapFundamentalGroupoidEquivalence h).functor.obj z)) =
    P.glue.hom.app z ≫
      P.right.map ((FundamentalGroupoid.map (intersectionToRightOpen h)).map
        ((overlapFundamentalGroupoidEquivalence h).unitIso.hom.app z)) := by
  simpa [ConstructionTargets.TwoOpenFundamentalGroupoidSpan.overlapFundamentalGroupoidMap,
    ConstructionTargets.TwoOpenFundamentalGroupoidSpan.overlapToPiece,
    FundamentalGroupoid.map] using
    P.glue.hom.naturality
      ((overlapFundamentalGroupoidEquivalence h).unitIso.hom.app z)

/-- Componentwise cancellation of the left functor-category unit, at the
actual overlap-to-left image.  This is the first cancellation in the left
span triangle and deliberately retains the overlap object in its argument. -/
theorem actualLeftRoundTrip_unit_cancel_app
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C))
    (z : FundamentalGroupoid (U h ∩ V h : Set (Gluing h))) :
    (actualLeftRoundTripIso h C P).hom.app
          ((FundamentalGroupoid.map (intersectionToLeftOpen h)).obj z) ≫
        (actualLeftRoundTripIso h C P).inv.app
          ((FundamentalGroupoid.map (intersectionToLeftOpen h)).obj z) =
      𝟙 _ :=
  (actualLeftRoundTripIso h C P).hom_inv_id_app _

/-- Right-hand componentwise cancellation at the actual overlap-to-right
image. -/
theorem actualRightRoundTrip_unit_cancel_app
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C))
    (z : FundamentalGroupoid (U h ∩ V h : Set (Gluing h))) :
    (actualRightRoundTripIso h C P).hom.app
          ((FundamentalGroupoid.map (intersectionToRightOpen h)).obj z) ≫
        (actualRightRoundTripIso h C P).inv.app
          ((FundamentalGroupoid.map (intersectionToRightOpen h)).obj z) =
      𝟙 _ :=
  (actualRightRoundTripIso h C P).hom_inv_id_app _

/-- Generic equivalence-span coherence specialized to the actual left collar
leg.  All overlap and piece equivalence transports remain explicit. -/
theorem actualLeft_span_roundTrip_triangle
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    (reverseLeftSpanComparison h C
        ((leftFunctorCategoryEquivalence h C).functor.obj P.left)).inv ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).functor
        (leftSpanComparison h C P.left).hom ≫
      ((overlapFundamentalGroupoidEquivalence h).funInvIdAssoc
        (FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙ P.left)).hom =
      Functor.whiskerLeft
        (FundamentalGroupoid.map (intersectionToLeftOpen h))
        (actualLeftRoundTripIso h C P).inv := by
  simpa [leftSpanComparison, reverseLeftSpanComparison,
    actualLeftRoundTripIso, leftFunctorCategoryEquivalence] using
    (ConstructionTargets.EquivalenceSpanRoundTrip.spanRoundTrip_triangle
      (eO := overlapFundamentalGroupoidEquivalence h)
      (eP := leftFundamentalGroupoidEquivalence h)
      (J := FundamentalGroupoid.map (intersectionToLeftOpen h))
      (K := coordinateLeftLeg)
      (q := left_span_coordinate_equation h)
      (L := P.left))

/-- Right collar-leg specialization of the equivalence-span triangle. -/
theorem actualRight_span_roundTrip_triangle
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    (reverseRightSpanComparison h C
        ((rightFunctorCategoryEquivalence h C).functor.obj P.right)).inv ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).functor
        (rightSpanComparison h C P.right).hom ≫
      ((overlapFundamentalGroupoidEquivalence h).funInvIdAssoc
        (FundamentalGroupoid.map (intersectionToRightOpen h) ⋙ P.right)).hom =
      Functor.whiskerLeft
        (FundamentalGroupoid.map (intersectionToRightOpen h))
        (actualRightRoundTripIso h C P).inv := by
  simpa [rightSpanComparison, reverseRightSpanComparison,
    actualRightRoundTripIso, rightFunctorCategoryEquivalence] using
    (ConstructionTargets.EquivalenceSpanRoundTrip.spanRoundTrip_triangle
      (eO := overlapFundamentalGroupoidEquivalence h)
      (eP := rightFundamentalGroupoidEquivalence h)
      (J := FundamentalGroupoid.map (intersectionToRightOpen h))
      (K := coordinateRightLeg h)
      (q := right_span_coordinate_equation h)
      (L := P.right))

/-- Outgoing orientation of the right collar span triangle, used after the
central overlap-glue naturality square. -/
theorem actualRight_span_roundTrip_triangle_inv
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    ((overlapFundamentalGroupoidEquivalence h).funInvIdAssoc
        (FundamentalGroupoid.map (intersectionToRightOpen h) ⋙ P.right)).inv ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).functor
        (rightSpanComparison h C P.right).inv ≫
      (reverseRightSpanComparison h C
        ((rightFunctorCategoryEquivalence h C).functor.obj P.right)).hom =
      Functor.whiskerLeft
        (FundamentalGroupoid.map (intersectionToRightOpen h))
        (actualRightRoundTripIso h C P).hom := by
  simpa [rightSpanComparison, reverseRightSpanComparison,
    actualRightRoundTripIso, rightFunctorCategoryEquivalence] using
    (ConstructionTargets.EquivalenceSpanRoundTrip.spanRoundTrip_triangle_inv
      (eO := overlapFundamentalGroupoidEquivalence h)
      (eP := rightFundamentalGroupoidEquivalence h)
      (J := FundamentalGroupoid.map (intersectionToRightOpen h))
      (K := coordinateRightLeg h)
      (q := right_span_coordinate_equation h)
      (L := P.right))

/-- The piecewise unit transformations form a morphism of actual collar
pseudococones. -/
theorem actualRoundTrip_glue_square
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    P.glue.hom ≫
        Functor.whiskerLeft
          (overlapFundamentalGroupoidMap (U := U h) (V := V h) false)
          (actualRightRoundTripIso h C P).hom =
      Functor.whiskerLeft
          (overlapFundamentalGroupoidMap (U := U h) (V := V h) true)
          (actualLeftRoundTripIso h C P).hom ≫
        (coordinateToActualPseudoCoconeObj h C
          (actualPseudoCoconeToCoordinateObj h C P)).glue.hom := by
  let eL := (overlapFundamentalGroupoidEquivalence h).funInvIdAssoc
    (FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙ P.left)
  let eR := (overlapFundamentalGroupoidEquivalence h).funInvIdAssoc
    (FundamentalGroupoid.map (intersectionToRightOpen h) ⋙ P.right)
  have hL :
      (reverseLeftSpanComparison h C
          ((leftFunctorCategoryEquivalence h C).functor.obj P.left)).inv ≫
        Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).functor
          (leftSpanComparison h C P.left).hom =
      Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToLeftOpen h))
          (actualLeftRoundTripIso h C P).inv ≫ eL.inv := by
    apply eL.eq_comp_inv.mpr
    simpa only [Category.assoc] using
      actualLeft_span_roundTrip_triangle h C P
  have hR :
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).functor
          (rightSpanComparison h C P.right).inv ≫
        (reverseRightSpanComparison h C
          ((rightFunctorCategoryEquivalence h C).functor.obj P.right)).hom =
      eR.hom ≫
        Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToRightOpen h))
          (actualRightRoundTripIso h C P).hom := by
    apply eR.inv_comp_eq.mp
    simpa only [Category.assoc] using
      actualRight_span_roundTrip_triangle_inv h C P
  have hC :
      eL.inv ≫ Functor.whiskerLeft
          (overlapFundamentalGroupoidEquivalence h).functor
          (transportedOverlapGlue h C P).hom =
      P.glue.hom ≫ eR.inv := by
    ext z
    simpa [eL, eR, transportedOverlapGlue,
      ConstructionTargets.TwoOpenFundamentalGroupoidSpan.overlapFundamentalGroupoidMap,
      ConstructionTargets.TwoOpenFundamentalGroupoidSpan.overlapToPiece,
      FundamentalGroupoid.map] using actualGlue_overlapUnit_naturality h C P z
  have hUL :
      Functor.whiskerLeft (overlapFundamentalGroupoidMap true)
          (actualLeftRoundTripIso h C P).hom ≫
      Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToLeftOpen h))
          (actualLeftRoundTripIso h C P).inv = 𝟙 _ := by
    ext z
    apply (actualLeftRoundTripIso h C P).hom_inv_id_app
  have hER : eR.inv ≫ eR.hom = 𝟙 _ := eR.inv_hom_id
  dsimp [coordinateToActualPseudoCoconeObj, actualPseudoCoconeToCoordinateObj,
    reverseTransportedOverlapGlue]
  change (reverseLeftSpanComparison h C
      ((leftFundamentalGroupoidEquivalence h).inverse ⋙ P.left)).inv ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).functor
        (leftSpanComparison h C P.left).hom =
    Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToLeftOpen h))
      (actualLeftRoundTripIso h C P).inv ≫ eL.inv at hL
  change Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).functor
      (rightSpanComparison h C P.right).inv ≫
      (reverseRightSpanComparison h C
        ((rightFundamentalGroupoidEquivalence h).inverse ⋙ P.right)).hom =
    eR.hom ≫
      Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToRightOpen h))
        (actualRightRoundTripIso h C P).hom at hR
  have hULe :
      Functor.whiskerLeft (overlapFundamentalGroupoidMap true)
          (actualLeftRoundTripIso h C P).hom ≫
        (Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToLeftOpen h))
      (actualLeftRoundTripIso h C P).inv ≫ eL.inv) = eL.inv := by
    rw [← Category.assoc, hUL]
    exact Category.id_comp _
  have hERu :
      (eR.inv ≫ eR.hom) ≫
        Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToRightOpen h))
          (actualRightRoundTripIso h C P).hom =
      Functor.whiskerLeft (overlapFundamentalGroupoidMap false)
        (actualRightRoundTripIso h C P).hom := by
    rw [hER, Category.id_comp]
    rfl
  have hULer {Z : FundamentalGroupoid (U h ∩ V h : Set (Gluing h)) ⥤ C}
      (k : ((overlapFundamentalGroupoidEquivalence h).functor ⋙
        (overlapFundamentalGroupoidEquivalence h).inverse ⋙
        FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙ P.left) ⟶ Z) :
      Functor.whiskerLeft (overlapFundamentalGroupoidMap true)
          (actualLeftRoundTripIso h C P).hom ≫
        ((Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToLeftOpen h))
          (actualLeftRoundTripIso h C P).inv ≫ eL.inv) ≫ k) =
      eL.inv ≫ k := by
    rw [← Category.assoc, hULe]
    rfl
  have hCr := reassoc_of% hC
  have hFinal :
      (P.glue.hom ≫ eR.inv) ≫ eR.hom ≫
          Functor.whiskerLeft (FundamentalGroupoid.map (intersectionToRightOpen h))
            (actualRightRoundTripIso h C P).hom =
        P.glue.hom ≫ Functor.whiskerLeft (overlapFundamentalGroupoidMap false)
          (actualRightRoundTripIso h C P).hom := by
    simpa only [Category.assoc] using
      congrArg (fun k => P.glue.hom ≫ k) hERu
  slice_rhs 2 3 => rw [hL]
  slice_rhs 1 4 => exact hULer _
  slice_rhs 1 3 => exact hCr _
  slice_rhs 2 3 => exact hR
  slice_rhs 1 4 => exact hFinal
  rfl

/-- Actual-side unit morphism for the forward/reverse pseudococone transport. -/
def actualRoundTripHom
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    P ⟶ (actualPseudoCoconeToCoordinateFunctor h C ⋙
      coordinateToActualPseudoCoconeFunctor h C).obj P where
  left := (actualLeftRoundTripIso h C P).hom
  right := (actualRightRoundTripIso h C P).hom
  glue_naturality := actualRoundTrip_glue_square h C P

/-- The inverse unit morphism; its glue square is obtained by cancelling the
two piece isomorphisms in the already-proved forward square. -/
def actualRoundTripInv
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    (actualPseudoCoconeToCoordinateFunctor h C ⋙
      coordinateToActualPseudoCoconeFunctor h C).obj P ⟶ P where
  left := (actualLeftRoundTripIso h C P).inv
  right := (actualRightRoundTripIso h C P).inv
  glue_naturality := by
    exact ConstructionTargets.TwoOpenPseudoCoconeStrictification.iso_square_inverse
      (Functor.isoWhiskerLeft (overlapFundamentalGroupoidMap true)
        (actualLeftRoundTripIso h C P))
      (Functor.isoWhiskerLeft (overlapFundamentalGroupoidMap false)
        (actualRightRoundTripIso h C P))
      P.glue.hom
      ((coordinateToActualPseudoCoconeObj h C
        (actualPseudoCoconeToCoordinateObj h C P)).glue.hom)
      (actualRoundTrip_glue_square h C P)

/-- Objectwise actual-pseudococone round-trip isomorphism. -/
def actualRoundTripIso
    (P : PseudoFunctorCocone (X := Gluing h) (U := U h) (V := V h) (C := C)) :
    P ≅ (actualPseudoCoconeToCoordinateFunctor h C ⋙
      coordinateToActualPseudoCoconeFunctor h C).obj P where
  hom := actualRoundTripHom h C P
  inv := actualRoundTripInv h C P
  hom_inv_id := by
    apply PseudoFunctorCoconeHom.ext
    · exact (actualLeftRoundTripIso h C P).hom_inv_id
    · exact (actualRightRoundTripIso h C P).hom_inv_id
  inv_hom_id := by
    apply PseudoFunctorCoconeHom.ext
    · exact (actualLeftRoundTripIso h C P).inv_hom_id
    · exact (actualRightRoundTripIso h C P).inv_hom_id

/-- Actual-side unit, oriented from the identity to forward transport followed
by reverse transport. -/
def actualRoundTripNatIso :
    Functor.id (PseudoFunctorCocone
      (X := Gluing h) (U := U h) (V := V h) (C := C)) ≅
      actualPseudoCoconeToCoordinateFunctor h C ⋙
        coordinateToActualPseudoCoconeFunctor h C :=
  NatIso.ofComponents (actualRoundTripIso h C) (by
    intro P Q tau
    apply PseudoFunctorCoconeHom.ext
    · exact actualLeftRoundTripIso_naturality h C tau
    · exact actualRightRoundTripIso_naturality h C tau)

/-- Incoming left-leg counit triangle for the coordinate round trip. -/
theorem coordinateLeft_span_roundTrip_counit_triangle
    (Q : CoordinatePseudoCocone h C) :
    (leftSpanComparison h C
        ((leftFunctorCategoryEquivalence h C).inverse.obj Q.left)).hom ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseLeftSpanComparison h C Q.left).inv ≫
      ((overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
        (coordinateLeftLeg ⋙ Q.left)).hom =
      Functor.whiskerLeft coordinateLeftLeg
        (coordinateLeftRoundTripIso h C Q).hom := by
  simpa [leftSpanComparison, reverseLeftSpanComparison,
    coordinateLeftRoundTripIso, leftFunctorCategoryEquivalence] using
    (ConstructionTargets.EquivalenceSpanRoundTrip.spanRoundTrip_counit_triangle
      (eO := overlapFundamentalGroupoidEquivalence h)
      (eP := leftFundamentalGroupoidEquivalence h)
      (J := FundamentalGroupoid.map (intersectionToLeftOpen h))
      (K := coordinateLeftLeg)
      (q := left_span_coordinate_equation h)
      (L := Q.left))

/-- Right-leg inverse counit triangle before cancelling the final counit
component. -/
theorem coordinateRight_span_roundTrip_counit_triangle_inv
    (Q : CoordinatePseudoCocone h C) :
    ((overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
        (coordinateRightLeg h ⋙ Q.right)).inv ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseRightSpanComparison h C Q.right).hom ≫
      (rightSpanComparison h C
        ((rightFunctorCategoryEquivalence h C).inverse.obj Q.right)).inv =
      Functor.whiskerLeft (coordinateRightLeg h)
        (coordinateRightRoundTripIso h C Q).inv := by
  simpa [rightSpanComparison, reverseRightSpanComparison,
    coordinateRightRoundTripIso, rightFunctorCategoryEquivalence] using
    (ConstructionTargets.EquivalenceSpanRoundTrip.spanRoundTrip_counit_triangle_inv
      (eO := overlapFundamentalGroupoidEquivalence h)
      (eP := rightFundamentalGroupoidEquivalence h)
      (J := FundamentalGroupoid.map (intersectionToRightOpen h))
      (K := coordinateRightLeg h)
      (q := right_span_coordinate_equation h)
      (L := Q.right))

/-- Coordinate glue naturality at the overlap-equivalence counit. -/
theorem coordinateGlue_overlapCounit_naturality
    (Q : CoordinatePseudoCocone h C)
    (z : FundamentalGroupoid BoundaryTorus) :
    Q.left.map (coordinateLeftLeg.map
        ((overlapFundamentalGroupoidEquivalence h).counitIso.hom.app z)) ≫
      Q.glue.hom.app z =
    Q.glue.hom.app
        ((overlapFundamentalGroupoidEquivalence h).functor.obj
          ((overlapFundamentalGroupoidEquivalence h).inverse.obj z)) ≫
      Q.right.map ((coordinateRightLeg h).map
        ((overlapFundamentalGroupoidEquivalence h).counitIso.hom.app z)) := by
  simpa using Q.glue.hom.naturality
    ((overlapFundamentalGroupoidEquivalence h).counitIso.hom.app z)

/-- The outgoing right span triangle followed by the right piece counit
cancels.  This is the exact terminal block in the coordinate glue square. -/
theorem coordinateRight_span_roundTrip_counit_cancel
    (Q : CoordinatePseudoCocone h C) :
    ((overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
        (coordinateRightLeg h ⋙ Q.right)).inv ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseRightSpanComparison h C Q.right).hom ≫
      (rightSpanComparison h C
        ((rightFunctorCategoryEquivalence h C).inverse.obj Q.right)).inv ≫
      Functor.whiskerLeft (coordinateRightLeg h)
        (coordinateRightRoundTripIso h C Q).hom = 𝟙 _ := by
  calc
    _ = Functor.whiskerLeft (coordinateRightLeg h)
          (coordinateRightRoundTripIso h C Q).inv ≫
      Functor.whiskerLeft (coordinateRightLeg h)
          (coordinateRightRoundTripIso h C Q).hom := by
      have ht := reassoc_of%
        (coordinateRight_span_roundTrip_counit_triangle_inv h C Q)
      simpa only [Category.assoc] using ht
        (Functor.whiskerLeft (coordinateRightLeg h)
          (coordinateRightRoundTripIso h C Q).hom)
    _ = _ := (Functor.isoWhiskerLeft (coordinateRightLeg h)
      (coordinateRightRoundTripIso h C Q)).inv_hom_id

/-- The central coordinate glue, transported through the inverse overlap
 equivalence, is conjugation by the two overlap counit comparisons. -/
theorem coordinateMiddle_counit_conjugation
    (Q : CoordinatePseudoCocone h C) :
    Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseTransportedOverlapGlue h C Q).hom =
      ((overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
          (coordinateLeftLeg ⋙ Q.left)).hom ≫
        Q.glue.hom ≫
        ((overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
          (coordinateRightLeg h ⋙ Q.right)).inv := by
  let eL := (overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
    (coordinateLeftLeg ⋙ Q.left)
  let eR := (overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
    (coordinateRightLeg h ⋙ Q.right)
  ext z
  have hz := coordinateGlue_overlapCounit_naturality h C Q z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_mono (eR.hom.app z)).1
  calc
    _ = eL.hom.app z ≫ Q.glue.hom.app z := by
      simpa [eL, eR, reverseTransportedOverlapGlue, Category.assoc] using hz.symm
    _ = (eL.hom.app z ≫ Q.glue.hom.app z ≫ eR.inv.app z) ≫
        eR.hom.app z := by
      symm
      simp only [Category.assoc, eR.inv_hom_id_app, Category.comp_id]

/-- The reverse pseudococone glue, after inverse-overlap whiskering, exposes
its three constituent blocks with their original association. -/
theorem coordinateRoundTrip_whiskered_reverseGlue
    (Q : CoordinatePseudoCocone h C) :
    Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (coordinateToActualPseudoCoconeObj h C Q).glue.hom =
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
          (reverseLeftSpanComparison h C Q.left).inv ≫
        Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
          (reverseTransportedOverlapGlue h C Q).hom ≫
        Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
          (reverseRightSpanComparison h C Q.right).hom := by
  dsimp [coordinateToActualPseudoCoconeObj]
  exact whiskerLeft_three_comp
    (C := C) (overlapFundamentalGroupoidEquivalence h).inverse
    (reverseLeftSpanComparison h C Q.left).inv
    (reverseTransportedOverlapGlue h C Q).hom
    (reverseRightSpanComparison h C Q.right).hom

/-- Substitute a normalized three-arrow prefix and four-arrow terminal block
without asking rewriting to discover their association inside a longer term. -/
theorem three_prefix_four_terminal_substitution
    {K : Type*} [Category K]
    {A B D E F G H I : K}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (x : A ⟶ E)
    (m : E ⟶ F) (d : F ⟶ G) (e : G ⟶ H) (f : H ⟶ I)
    (g : I ⟶ F)
    (hp : a ≫ b ≫ c = x) (ht : d ≫ e ≫ f ≫ g = 𝟙 F) :
    ((a ≫ b ≫ c) ≫ m) ≫ (d ≫ e ≫ f ≫ g) = x ≫ m := by
  rw [hp, ht, Category.comp_id]

/-- Replace the middle arrow in the four-map association emitted by a
pseudococone glue followed by a component map. -/
theorem four_context_middle_substitution
    {K : Type*} [Category K] {A B D E F : K}
    (a : A ⟶ B) (b b' : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (h : b = b') : (a ≫ b ≫ c) ≫ d = (a ≫ b' ≫ c) ≫ d := by
  rw [h]

/-- The exact right-associated suffix shape left after
`four_context_middle_substitution`. -/
theorem right_nested_prefix_terminal_substitution
    {K : Type*} [Category K] {A B D E F G H I : K}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (x : A ⟶ E)
    (m : E ⟶ F) (d : F ⟶ G) (e : G ⟶ H) (f : H ⟶ I)
    (g : I ⟶ F)
    (hp : a ≫ b ≫ c = x) (ht : d ≫ e ≫ f ≫ g = 𝟙 F) :
    (a ≫ (b ≫ (c ≫ m ≫ d) ≫ e) ≫ f) ≫ g = x ≫ m := by
  simpa only [Category.assoc] using
    three_prefix_four_terminal_substitution a b c x m d e f g hp ht

/-- Coordinate-side round-trip counit glue square. -/
theorem coordinateRoundTrip_glue_square
    (Q : CoordinatePseudoCocone h C) :
    (actualPseudoCoconeToCoordinateObj h C
        (coordinateToActualPseudoCoconeObj h C Q)).glue.hom ≫
      Functor.whiskerLeft (coordinateRightLeg h)
        (coordinateRightRoundTripIso h C Q).hom =
      Functor.whiskerLeft coordinateLeftLeg
          (coordinateLeftRoundTripIso h C Q).hom ≫ Q.glue.hom := by
  let eL := (overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
    (coordinateLeftLeg ⋙ Q.left)
  let eR := (overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
    (coordinateRightLeg h ⋙ Q.right)
  have hW := coordinateRoundTrip_whiskered_reverseGlue h C Q
  have hM := coordinateMiddle_counit_conjugation h C Q
  have hP := coordinateLeft_span_roundTrip_counit_triangle h C Q
  have hT := coordinateRight_span_roundTrip_counit_cancel h C Q
  dsimp [actualPseudoCoconeToCoordinateObj, transportedOverlapGlue]
  have hChain := congrArg
    (fun k => Functor.whiskerLeft
        (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseLeftSpanComparison h C Q.left).inv ≫ k ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseRightSpanComparison h C Q.right).hom) hM
  have hWG := hW.trans hChain
  refine (four_context_middle_substitution
    (leftSpanComparison h C
      (coordinateToActualPseudoCoconeObj h C Q).left).hom
    (Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
      (coordinateToActualPseudoCoconeObj h C Q).glue.hom)
    (Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseLeftSpanComparison h C Q.left).inv ≫
      (((overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
          (coordinateLeftLeg ⋙ Q.left)).hom ≫ Q.glue.hom ≫
        ((overlapFundamentalGroupoidEquivalence h).invFunIdAssoc
          (coordinateRightLeg h ⋙ Q.right)).inv) ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseRightSpanComparison h C Q.right).hom)
    (rightSpanComparison h C
      (coordinateToActualPseudoCoconeObj h C Q).right).inv
    (Functor.whiskerLeft (coordinateRightLeg h)
      (coordinateRightRoundTripIso h C Q).hom) hWG).trans ?_
  exact right_nested_prefix_terminal_substitution
      (leftSpanComparison h C
        (coordinateToActualPseudoCoconeObj h C Q).left).hom
      (Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseLeftSpanComparison h C Q.left).inv)
      eL.hom
      (Functor.whiskerLeft coordinateLeftLeg
        (coordinateLeftRoundTripIso h C Q).hom)
      Q.glue.hom eR.inv
      (Functor.whiskerLeft (overlapFundamentalGroupoidEquivalence h).inverse
        (reverseRightSpanComparison h C Q.right).hom)
      (rightSpanComparison h C
        (coordinateToActualPseudoCoconeObj h C Q).right).inv
      (Functor.whiskerLeft (coordinateRightLeg h)
        (coordinateRightRoundTripIso h C Q).hom)
      hP hT

/-- Coordinate-side counit morphism for reverse then forward transport. -/
def coordinateRoundTripHom (Q : CoordinatePseudoCocone h C) :
    (coordinateToActualPseudoCoconeFunctor h C ⋙
      actualPseudoCoconeToCoordinateFunctor h C).obj Q ⟶ Q where
  left := (coordinateLeftRoundTripIso h C Q).hom
  right := (coordinateRightRoundTripIso h C Q).hom
  glue_naturality := coordinateRoundTrip_glue_square h C Q

/-- Inverse coordinate-side counit morphism, obtained by inverting the
already-proved glue square. -/
def coordinateRoundTripInv (Q : CoordinatePseudoCocone h C) :
    Q ⟶ (coordinateToActualPseudoCoconeFunctor h C ⋙
      actualPseudoCoconeToCoordinateFunctor h C).obj Q where
  left := (coordinateLeftRoundTripIso h C Q).inv
  right := (coordinateRightRoundTripIso h C Q).inv
  glue_naturality := by
    exact ConstructionTargets.TwoOpenPseudoCoconeStrictification.iso_square_inverse
      (Functor.isoWhiskerLeft coordinateLeftLeg
        (coordinateLeftRoundTripIso h C Q))
      (Functor.isoWhiskerLeft (coordinateRightLeg h)
        (coordinateRightRoundTripIso h C Q))
      ((actualPseudoCoconeToCoordinateObj h C
        (coordinateToActualPseudoCoconeObj h C Q)).glue.hom)
      Q.glue.hom
      (coordinateRoundTrip_glue_square h C Q)

/-- Objectwise coordinate-pseudococone round-trip isomorphism. -/
def coordinateRoundTripIso (Q : CoordinatePseudoCocone h C) :
    (coordinateToActualPseudoCoconeFunctor h C ⋙
      actualPseudoCoconeToCoordinateFunctor h C).obj Q ≅ Q where
  hom := coordinateRoundTripHom h C Q
  inv := coordinateRoundTripInv h C Q
  hom_inv_id := by
    apply CoordinatePseudoCoconeHom.ext
    · exact (coordinateLeftRoundTripIso h C Q).hom_inv_id
    · exact (coordinateRightRoundTripIso h C Q).hom_inv_id
  inv_hom_id := by
    apply CoordinatePseudoCoconeHom.ext
    · exact (coordinateLeftRoundTripIso h C Q).inv_hom_id
    · exact (coordinateRightRoundTripIso h C Q).inv_hom_id

/-- Coordinate-side counit, oriented from reverse/forward transport to the
identity functor. -/
def coordinateRoundTripNatIso :
    coordinateToActualPseudoCoconeFunctor h C ⋙
        actualPseudoCoconeToCoordinateFunctor h C ≅
      Functor.id (CoordinatePseudoCocone h C) :=
  NatIso.ofComponents (coordinateRoundTripIso h C) (by
    intro P Q tau
    apply CoordinatePseudoCoconeHom.ext
    · exact coordinateLeftRoundTripIso_naturality h C tau
    · exact coordinateRightRoundTripIso_naturality h C tau)

/-- Equivalence between actual collar pseudococones and their solid-torus /
boundary-torus coordinate form. -/
def actualCoordinatePseudoCoconeEquivalence :
    PseudoFunctorCocone
        (X := Gluing h) (U := U h) (V := V h) (C := C) ≌
      CoordinatePseudoCocone h C :=
  CategoryTheory.Equivalence.mk'
    (actualPseudoCoconeToCoordinateFunctor h C)
    (coordinateToActualPseudoCoconeFunctor h C)
    (actualRoundTripNatIso h C)
    (coordinateRoundTripNatIso h C)
    (by
      intro P
      apply CoordinatePseudoCoconeHom.ext
      · exact (leftFunctorCategoryEquivalence h C).functor_unitIso_comp P.left
      · exact (rightFunctorCategoryEquivalence h C).functor_unitIso_comp P.right)

/-- Mapping-category form of the collared two-open fundamental-groupoid
pseudopushout, expressed in solid-torus and boundary-torus coordinates. -/
def gluingFundamentalGroupoidCoordinateEquivalence :
    Functor (FundamentalGroupoid (Gluing h)) C ≌ CoordinatePseudoCocone h C :=
  (gluingFundamentalGroupoidPseudopushoutEquivalence h C).trans
    (actualCoordinatePseudoCoconeEquivalence h C)

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
#print axioms whiskerLeft_three_comp
#print axioms actualPseudoCoconeToCoordinateMap
#print axioms actualPseudoCoconeToCoordinateFunctor
#print axioms reverseLeftSpanComparison
#print axioms reverseRightSpanComparison
#print axioms reverseTransportedOverlapGlue
#print axioms coordinateToActualPseudoCoconeObj
#print axioms reverseLeftSpanComparison_naturality
#print axioms reverseRightSpanComparison_naturality
#print axioms reverseLeftSpanComparison_inv_naturality
#print axioms reverseTransportedOverlapGlue_naturality
#print axioms coordinateToActualPseudoCoconeMap
#print axioms coordinateToActualPseudoCoconeFunctor
#print axioms actualLeftRoundTripIso
#print axioms actualRightRoundTripIso
#print axioms coordinateLeftRoundTripIso
#print axioms coordinateRightRoundTripIso
#print axioms actualLeftRoundTripIso_naturality
#print axioms actualRightRoundTripIso_naturality
#print axioms coordinateLeftRoundTripIso_naturality
#print axioms coordinateRightRoundTripIso_naturality
#print axioms actualGlue_overlapUnit_naturality
#print axioms actualLeftRoundTrip_unit_cancel_app
#print axioms actualRightRoundTrip_unit_cancel_app
#print axioms actualLeft_span_roundTrip_triangle
#print axioms actualRight_span_roundTrip_triangle
#print axioms actualRight_span_roundTrip_triangle_inv
#print axioms actualRoundTrip_glue_square
#print axioms actualRoundTripHom
#print axioms actualRoundTripInv
#print axioms actualRoundTripIso
#print axioms actualRoundTripNatIso
#print axioms coordinateLeft_span_roundTrip_counit_triangle
#print axioms coordinateRight_span_roundTrip_counit_triangle_inv
#print axioms coordinateGlue_overlapCounit_naturality
#print axioms coordinateRight_span_roundTrip_counit_cancel
#print axioms coordinateMiddle_counit_conjugation
#print axioms coordinateRoundTrip_whiskered_reverseGlue
#print axioms three_prefix_four_terminal_substitution
#print axioms four_context_middle_substitution
#print axioms right_nested_prefix_terminal_substitution
#print axioms coordinateRoundTrip_glue_square
#print axioms coordinateRoundTripHom
#print axioms coordinateRoundTripInv
#print axioms coordinateRoundTripIso
#print axioms coordinateRoundTripNatIso
#print axioms actualCoordinatePseudoCoconeEquivalence
#print axioms gluingFundamentalGroupoidCoordinateEquivalence

end ConstructionTargets.TwiceSpiralPseudococoneTransport
