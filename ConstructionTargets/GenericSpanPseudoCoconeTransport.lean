import ConstructionTargets.EquivalenceSpanRoundTrip
import Mathlib.CategoryTheory.CatCommSq

open CategoryTheory
noncomputable section

universe uK uL uR uK' uL' uR' uC uD

namespace ConstructionTargets.GenericSpanPseudoCoconeTransport

variable {K : Type uK} {L : Type uL} {R : Type uR}
  {K' : Type uK'} {L' : Type uL'} {R' : Type uR'}
  [Category K] [Category L] [Category R]
  [Category K'] [Category L'] [Category R']

structure SpanPseudoCocone (l : K ⥤ L) (r : K ⥤ R)
    (C : Type uC) [Category C] where
  left : L ⥤ C
  right : R ⥤ C
  glue : l ⋙ left ≅ r ⋙ right

structure SpanPseudoCoconeHom {l : K ⥤ L} {r : K ⥤ R}
    {C : Type uC} [Category C]
    (P Q : SpanPseudoCocone l r C) where
  left : P.left ⟶ Q.left
  right : P.right ⟶ Q.right
  glue_naturality : P.glue.hom ≫ Functor.whiskerLeft r right =
    Functor.whiskerLeft l left ≫ Q.glue.hom

@[ext] theorem SpanPseudoCoconeHom.ext {l : K ⥤ L} {r : K ⥤ R}
    {C : Type uC} [Category C] {P Q : SpanPseudoCocone l r C}
    {f g : SpanPseudoCoconeHom P Q}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f; cases g; simp_all

instance {l : K ⥤ L} {r : K ⥤ R} {C : Type uC} [Category C] :
    Category (SpanPseudoCocone l r C) where
  Hom := SpanPseudoCoconeHom
  id P := { left := 𝟙 P.left, right := 𝟙 P.right, glue_naturality := by simp }
  comp f g := {
    left := f.left ≫ g.left
    right := f.right ≫ g.right
    glue_naturality := by
      rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
      rw [← Category.assoc, f.glue_naturality]
      simp only [Category.assoc]
      rw [g.glue_naturality] }
  id_comp _ := by ext <;> simp
  comp_id _ := by ext <;> simp
  assoc _ _ _ := by ext <;> simp [Category.assoc]

def postcomposeObj {l : K ⥤ L} {r : K ⥤ R}
    {C : Type uC} {D : Type uD} [Category C] [Category D]
    (H : C ⥤ D) (P : SpanPseudoCocone l r C) : SpanPseudoCocone l r D where
  left := P.left ⋙ H
  right := P.right ⋙ H
  glue := Functor.isoWhiskerRight P.glue H

def postcomposeFunctor {l : K ⥤ L} {r : K ⥤ R}
    {C : Type uC} {D : Type uD} [Category C] [Category D] (H : C ⥤ D) :
    SpanPseudoCocone l r C ⥤ SpanPseudoCocone l r D where
  obj := postcomposeObj H
  map f := {
    left := Functor.whiskerRight f.left H
    right := Functor.whiskerRight f.right H
    glue_naturality := by
      ext z
      simpa [postcomposeObj] using congrArg H.map (NatTrans.congr_app f.glue_naturality z) }
  map_id P := by
    apply SpanPseudoCoconeHom.ext <;> ext z
    · change H.map (𝟙 _) = 𝟙 _; simp
    · change H.map (𝟙 _) = 𝟙 _; simp
  map_comp f g := by
    apply SpanPseudoCoconeHom.ext <;> ext z
    · change H.map (f.left.app z ≫ g.left.app z) =
        H.map (f.left.app z) ≫ H.map (g.left.app z); simp
    · change H.map (f.right.app z ≫ g.right.app z) =
        H.map (f.right.app z) ≫ H.map (g.right.app z); simp

variable (l : K ⥤ L) (r : K ⥤ R) (l' : K' ⥤ L') (r' : K' ⥤ R')
  (eK : K ≌ K') (eL : L ≌ L') (eR : R ≌ R')
  (αL : eK.inverse ⋙ l ⋙ eL.functor ≅ l')
  (αR : eK.inverse ⋙ r ⋙ eR.functor ≅ r')

def leftComparison {C : Type uC} [Category C] (F : L ⥤ C) :
    l' ⋙ eL.inverse ⋙ F ≅ eK.inverse ⋙ l ⋙ F :=
  (Functor.isoWhiskerRight αL.symm (eL.inverse ⋙ F)).trans
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (eK.inverse ⋙ l) eL.unitIso.symm) F)

def rightComparison {C : Type uC} [Category C] (F : R ⥤ C) :
    r' ⋙ eR.inverse ⋙ F ≅ eK.inverse ⋙ r ⋙ F :=
  (Functor.isoWhiskerRight αR.symm (eR.inverse ⋙ F)).trans
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (eK.inverse ⋙ r) eR.unitIso.symm) F)

def transportObj {C : Type uC} [Category C] (P : SpanPseudoCocone l r C) :
    SpanPseudoCocone l' r' C where
  left := eL.inverse ⋙ P.left
  right := eR.inverse ⋙ P.right
  glue := (leftComparison l l' eK eL αL P.left).trans
    ((Functor.isoWhiskerLeft eK.inverse P.glue).trans
      (rightComparison r r' eK eR αR P.right).symm)

theorem comparison_naturality_left {C : Type uC} [Category C]
    {F G : L ⥤ C} (τ : F ⟶ G) :
    (leftComparison l l' eK eL αL F).hom ≫
        Functor.whiskerLeft (eK.inverse ⋙ l) τ =
      Functor.whiskerLeft l' (Functor.whiskerLeft eL.inverse τ) ≫
        (leftComparison l l' eK eL αL G).hom := by
  ext z
  simp [leftComparison, Category.assoc]

theorem comparison_naturality_right_inv {C : Type uC} [Category C]
    {F G : R ⥤ C} (τ : F ⟶ G) :
    (rightComparison r r' eK eR αR F).inv ≫
        Functor.whiskerLeft r' (Functor.whiskerLeft eR.inverse τ) =
      Functor.whiskerLeft (eK.inverse ⋙ r) τ ≫
        (rightComparison r r' eK eR αR G).inv := by
  ext z
  simp [rightComparison, Category.assoc]

theorem transportedGlue_naturality {C : Type uC} [Category C]
    {P Q : SpanPseudoCocone l r C} (τ : P ⟶ Q) :
    (Functor.isoWhiskerLeft eK.inverse P.glue).hom ≫
        Functor.whiskerLeft (eK.inverse ⋙ r) τ.right =
      Functor.whiskerLeft (eK.inverse ⋙ l) τ.left ≫
        (Functor.isoWhiskerLeft eK.inverse Q.glue).hom := by
  ext z
  exact NatTrans.congr_app τ.glue_naturality (eK.inverse.obj z)

theorem three_square_pasting {C : Type uC} [Category C]
    {A B D E A' B' D' E' : C}
    (ll : A ⟶ B) (m : B ⟶ D) (rr : D ⟶ E)
    (ll' : A' ⟶ B') (m' : B' ⟶ D') (rr' : D' ⟶ E')
    (a : B ⟶ B') (b : D ⟶ D') (x : A ⟶ A') (y : E ⟶ E')
    (hl : ll ≫ a = x ≫ ll') (hm : m ≫ b = a ≫ m')
    (hr : rr ≫ y = b ≫ rr') :
    (ll ≫ m ≫ rr) ≫ y = x ≫ (ll' ≫ m' ≫ rr') := by
  simp only [Category.assoc]
  rw [hr, ← Category.assoc m, hm, Category.assoc, ← Category.assoc ll, hl]
  exact Category.assoc x ll' (m' ≫ rr')

def transportMap {C : Type uC} [Category C]
    {P Q : SpanPseudoCocone l r C} (τ : P ⟶ Q) :
    transportObj l r l' r' eK eL eR αL αR P ⟶
      transportObj l r l' r' eK eL eR αL αR Q where
  left := Functor.whiskerLeft eL.inverse τ.left
  right := Functor.whiskerLeft eR.inverse τ.right
  glue_naturality := by
    exact three_square_pasting
      (leftComparison l l' eK eL αL P.left).hom
      (Functor.isoWhiskerLeft eK.inverse P.glue).hom
      (rightComparison r r' eK eR αR P.right).inv
      (leftComparison l l' eK eL αL Q.left).hom
      (Functor.isoWhiskerLeft eK.inverse Q.glue).hom
      (rightComparison r r' eK eR αR Q.right).inv
      (Functor.whiskerLeft (eK.inverse ⋙ l) τ.left)
      (Functor.whiskerLeft (eK.inverse ⋙ r) τ.right)
      (Functor.whiskerLeft l' (Functor.whiskerLeft eL.inverse τ.left))
      (Functor.whiskerLeft r' (Functor.whiskerLeft eR.inverse τ.right))
      (comparison_naturality_left l l' eK eL αL τ.left)
      (transportedGlue_naturality l r eK τ)
      (comparison_naturality_right_inv r r' eK eR αR τ.right)

def transportFunctor {C : Type uC} [Category C] :
    SpanPseudoCocone l r C ⥤ SpanPseudoCocone l' r' C where
  obj := transportObj l r l' r' eK eL eR αL αR
  map := transportMap l r l' r' eK eL eR αL αR
  map_id P := by apply SpanPseudoCoconeHom.ext <;> rfl
  map_comp f g := by apply SpanPseudoCoconeHom.ext <;> rfl

variable {C : Type uC} {D : Type uD} [Category C] [Category D]

def transportPostcomposeIsoApp (H : C ⥤ D) (P : SpanPseudoCocone l r C) :
    (transportFunctor l r l' r' eK eL eR αL αR (C := D)).obj
        ((postcomposeFunctor H).obj P) ≅
      (postcomposeFunctor H).obj
        ((transportFunctor l r l' r' eK eL eR αL αR (C := C)).obj P) := by
  let aL := Functor.associator eL.inverse P.left H
  let aR := Functor.associator eR.inverse P.right H
  refine { hom := { left := aL.hom, right := aR.hom, glue_naturality := ?_ }
           inv := { left := aL.inv, right := aR.inv, glue_naturality := ?_ }
           hom_inv_id := ?_, inv_hom_id := ?_ }
  · ext z
    simp [transportFunctor, transportObj, postcomposeFunctor, postcomposeObj,
      leftComparison, rightComparison, aL, aR]
  · ext z
    simp [transportFunctor, transportObj, postcomposeFunctor, postcomposeObj,
      leftComparison, rightComparison, aL, aR]
  · apply SpanPseudoCoconeHom.ext
    · exact aL.hom_inv_id
    · exact aR.hom_inv_id
  · apply SpanPseudoCoconeHom.ext
    · exact aL.inv_hom_id
    · exact aR.inv_hom_id

def transportPostcomposeIso (H : C ⥤ D) :
    postcomposeFunctor H ⋙
        transportFunctor l r l' r' eK eL eR αL αR (C := D) ≅
      transportFunctor l r l' r' eK eL eR αL αR (C := C) ⋙
        postcomposeFunctor H :=
  NatIso.ofComponents
    (transportPostcomposeIsoApp l r l' r' eK eL eR αL αR H) (by
      intro P Q τ
      apply SpanPseudoCoconeHom.ext
      · ext z
        change H.map (τ.left.app (eL.inverse.obj z)) ≫ 𝟙 _ =
          𝟙 _ ≫ H.map (τ.left.app (eL.inverse.obj z))
        simp
      · ext z
        change H.map (τ.right.app (eR.inverse.obj z)) ≫ 𝟙 _ =
          𝟙 _ ≫ H.map (τ.right.app (eR.inverse.obj z))
        simp)

#print axioms transportFunctor
#print axioms transportPostcomposeIso


open ConstructionTargets.EquivalenceSpanRoundTrip

def reverseLeftComparison {C : Type uC} [Category C] (F : L' ⥤ C) :
    eK.functor ⋙ l' ⋙ F ≅ l ⋙ eL.functor ⋙ F :=
  (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft eK.functor αL.symm) F).trans
  (Functor.isoWhiskerRight (eK.funInvIdAssoc (l ⋙ eL.functor)) F)

def reverseRightComparison {C : Type uC} [Category C] (F : R' ⥤ C) :
    eK.functor ⋙ r' ⋙ F ≅ r ⋙ eR.functor ⋙ F :=
  (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft eK.functor αR.symm) F).trans
  (Functor.isoWhiskerRight (eK.funInvIdAssoc (r ⋙ eR.functor)) F)

theorem isoSpanRoundTrip_triangle {C : Type uC} [Category C] (F : L ⥤ C) :
    (reverseLeftComparison l l' eK eL αL (eL.inverse ⋙ F)).inv ≫
      Functor.whiskerLeft eK.functor
        (leftComparison l l' eK eL αL F).hom ≫
      (eK.funInvIdAssoc (l ⋙ F)).hom =
    Functor.whiskerLeft l ((eL.congrLeft).unitIso.inv.app F) := by
  simpa only [leftComparison, reverseLeftComparison] using
    (spanRoundTripIso_unit eK eL l l' αL F)

theorem isoSpanRoundTrip_counit_triangle {C : Type uC} [Category C]
    (F : L' ⥤ C) :
    (leftComparison l l' eK eL αL (eL.functor ⋙ F)).hom ≫
      Functor.whiskerLeft eK.inverse
        (reverseLeftComparison l l' eK eL αL F).inv ≫
      (eK.invFunIdAssoc (l' ⋙ F)).hom =
    Functor.whiskerLeft l' ((eL.congrLeft).counitIso.hom.app F) := by
  simpa only [leftComparison, reverseLeftComparison] using
    (spanRoundTripIso_counit eK eL l l' αL F)

def reverseTransportObj {C : Type uC} [Category C]
    (Q : SpanPseudoCocone l' r' C) : SpanPseudoCocone l r C where
  left := eL.functor ⋙ Q.left
  right := eR.functor ⋙ Q.right
  glue := (reverseLeftComparison l l' eK eL αL Q.left).symm.trans
    ((Functor.isoWhiskerLeft eK.functor Q.glue).trans
      (reverseRightComparison r r' eK eR αR Q.right))

theorem reverseComparison_naturality_left_inv {C : Type uC} [Category C]
    {F G : L' ⥤ C} (τ : F ⟶ G) :
    (reverseLeftComparison l l' eK eL αL F).inv ≫
      Functor.whiskerLeft (eK.functor ⋙ l') τ =
    Functor.whiskerLeft l (Functor.whiskerLeft eL.functor τ) ≫
      (reverseLeftComparison l l' eK eL αL G).inv := by
  ext z
  simp [reverseLeftComparison, Category.assoc]

theorem reverseComparison_naturality_right {C : Type uC} [Category C]
    {F G : R' ⥤ C} (τ : F ⟶ G) :
    (reverseRightComparison r r' eK eR αR F).hom ≫
      Functor.whiskerLeft r (Functor.whiskerLeft eR.functor τ) =
    Functor.whiskerLeft (eK.functor ⋙ r') τ ≫
      (reverseRightComparison r r' eK eR αR G).hom := by
  ext z
  simp [reverseRightComparison, Category.assoc]

def reverseTransportMap {C : Type uC} [Category C]
    {P Q : SpanPseudoCocone l' r' C} (τ : P ⟶ Q) :
    reverseTransportObj l r l' r' eK eL eR αL αR P ⟶
      reverseTransportObj l r l' r' eK eL eR αL αR Q where
  left := Functor.whiskerLeft eL.functor τ.left
  right := Functor.whiskerLeft eR.functor τ.right
  glue_naturality := by
    exact three_square_pasting
      (reverseLeftComparison l l' eK eL αL P.left).inv
      (Functor.isoWhiskerLeft eK.functor P.glue).hom
      (reverseRightComparison r r' eK eR αR P.right).hom
      (reverseLeftComparison l l' eK eL αL Q.left).inv
      (Functor.isoWhiskerLeft eK.functor Q.glue).hom
      (reverseRightComparison r r' eK eR αR Q.right).hom
      (Functor.whiskerLeft (eK.functor ⋙ l') τ.left)
      (Functor.whiskerLeft (eK.functor ⋙ r') τ.right)
      (Functor.whiskerLeft l (Functor.whiskerLeft eL.functor τ.left))
      (Functor.whiskerLeft r (Functor.whiskerLeft eR.functor τ.right))
      (reverseComparison_naturality_left_inv l l' eK eL αL τ.left)
      (by ext z; exact NatTrans.congr_app τ.glue_naturality (eK.functor.obj z))
      (reverseComparison_naturality_right r r' eK eR αR τ.right)

def reverseTransportFunctor {C : Type uC} [Category C] :
    SpanPseudoCocone l' r' C ⥤ SpanPseudoCocone l r C where
  obj := reverseTransportObj l r l' r' eK eL eR αL αR
  map := reverseTransportMap l r l' r' eK eL eR αL αR
  map_id P := by apply SpanPseudoCoconeHom.ext <;> rfl
  map_comp f g := by apply SpanPseudoCoconeHom.ext <;> rfl

theorem spanRoundTripIso_unit_inv_with_prefix
    {A B A' B' C : Type*}
    [Category A] [Category B] [Category A'] [Category B'] [Category C]
    (eA : A ≌ A') (eB : B ≌ B') (j : A ⥤ B) (j' : A' ⥤ B')
    (α : eA.inverse ⋙ j ⋙ eB.functor ≅ j') (F : B ⥤ C) :
    (eA.funInvIdAssoc (j ⋙ F)).inv ≫
        Functor.whiskerLeft eA.functor
          (forwardSpanComparisonIso eA eB j j' α F).inv ≫
        (reverseSpanComparisonIso eA eB j j' α
          (eB.inverse ⋙ F)).hom =
      Functor.whiskerLeft j ((eB.congrLeft).unitIso.hom.app F) := by
  rw [spanRoundTripIso_unit_inv]

theorem inverse_glue_square_of_forward
    {A : Type*} [Category A]
    {X Y X' Y' : A} (g : X ⟶ Y) (g' : X' ⟶ Y')
    (iL : X ≅ X') (iR : Y ≅ Y')
    (h : g ≫ iR.hom = iL.hom ≫ g') :
    g' ≫ iR.inv = iL.inv ≫ g := by
  apply (cancel_epi iL.hom).1
  rw [iL.hom_inv_id_assoc]
  rw [← Category.assoc, ← h, Category.assoc, iR.hom_inv_id,
    Category.comp_id]

theorem unitGlueSquare {C : Type uC} [Category C]
    (P : SpanPseudoCocone l r C) :
    P.glue.hom ≫ Functor.whiskerLeft r
      ((eR.congrLeft).unitIso.hom.app P.right) =
    Functor.whiskerLeft l ((eL.congrLeft).unitIso.hom.app P.left) ≫
      (reverseTransportObj l r l' r' eK eL eR αL αR
        (transportObj l r l' r' eK eL eR αL αR P)).glue.hom := by
  let oL := eK.funInvIdAssoc (l ⋙ P.left)
  let oR := eK.funInvIdAssoc (r ⋙ P.right)
  have hL :
      (reverseLeftComparison l l' eK eL αL (eL.inverse ⋙ P.left)).inv ≫
        Functor.whiskerLeft eK.functor
          (leftComparison l l' eK eL αL P.left).hom =
      Functor.whiskerLeft l ((eL.congrLeft).unitIso.inv.app P.left) ≫ oL.inv := by
    apply oL.eq_comp_inv.mpr
    simpa only [Category.assoc, leftComparison, reverseLeftComparison] using
      (ConstructionTargets.EquivalenceSpanRoundTrip.spanRoundTripIso_unit
        eK eL l l' αL P.left)
  have hRP :
      oR.inv ≫ Functor.whiskerLeft eK.functor
          (rightComparison r r' eK eR αR P.right).inv ≫
        (reverseRightComparison r r' eK eR αR
          (eR.inverse ⋙ P.right)).hom =
      Functor.whiskerLeft r
        ((eR.congrLeft).unitIso.hom.app P.right) := by
    simpa only [rightComparison, reverseRightComparison] using
      spanRoundTripIso_unit_inv_with_prefix
        eK eR r r' αR P.right
  have hC : oL.inv ≫ Functor.whiskerLeft eK.functor
      (Functor.isoWhiskerLeft eK.inverse P.glue).hom = P.glue.hom ≫ oR.inv := by
    ext z
    simpa [oL, oR, Category.assoc] using
      (P.glue.hom.naturality (eK.unit.app z))
  have hUL :
      Functor.whiskerLeft l ((eL.congrLeft).unitIso.hom.app P.left) ≫
        Functor.whiskerLeft l ((eL.congrLeft).unitIso.inv.app P.left) = 𝟙 _ :=
    (Functor.isoWhiskerLeft l ((eL.congrLeft).unitIso.app P.left)).hom_inv_id
  have hULe {Z : Functor K C}
      (k : (eK.functor ⋙ eK.inverse ⋙ l ⋙ P.left) ⟶ Z) :
      Functor.whiskerLeft l ((eL.congrLeft).unitIso.hom.app P.left) ≫
        ((Functor.whiskerLeft l ((eL.congrLeft).unitIso.inv.app P.left) ≫
          oL.inv) ≫ k) = oL.inv ≫ k := by
    rw [← Category.assoc, ← Category.assoc, hUL, Category.id_comp]
    rfl
  have hCr := reassoc_of% hC
  dsimp [reverseTransportObj, transportObj]
  slice_rhs 2 3 => rw [hL]
  slice_rhs 1 4 => exact hULe _
  slice_rhs 1 3 => exact hCr _
  slice_rhs 2 4 => exact hRP
  rfl

def unitHom {C : Type uC} [Category C] (P : SpanPseudoCocone l r C) :
    P ⟶ (transportFunctor l r l' r' eK eL eR αL αR ⋙
      reverseTransportFunctor l r l' r' eK eL eR αL αR).obj P where
  left := (eL.congrLeft).unitIso.hom.app P.left
  right := (eR.congrLeft).unitIso.hom.app P.right
  glue_naturality := unitGlueSquare l r l' r' eK eL eR αL αR P

def unitInv {C : Type uC} [Category C] (P : SpanPseudoCocone l r C) :
    (transportFunctor l r l' r' eK eL eR αL αR ⋙
      reverseTransportFunctor l r l' r' eK eL eR αL αR).obj P ⟶ P where
  left := (eL.congrLeft).unitIso.inv.app P.left
  right := (eR.congrLeft).unitIso.inv.app P.right
  glue_naturality := inverse_glue_square_of_forward P.glue.hom
    (reverseTransportObj l r l' r' eK eL eR αL αR
      (transportObj l r l' r' eK eL eR αL αR P)).glue.hom
    (Functor.isoWhiskerLeft l ((eL.congrLeft).unitIso.app P.left))
    (Functor.isoWhiskerLeft r ((eR.congrLeft).unitIso.app P.right))
    (unitGlueSquare l r l' r' eK eL eR αL αR P)

def unitIsoApp {C : Type uC} [Category C] (P : SpanPseudoCocone l r C) :
    P ≅ (transportFunctor l r l' r' eK eL eR αL αR ⋙
      reverseTransportFunctor l r l' r' eK eL eR αL αR).obj P := by
  let iL := (eL.congrLeft).unitIso.app P.left
  let iR := (eR.congrLeft).unitIso.app P.right
  refine { hom := unitHom l r l' r' eK eL eR αL αR P
           inv := unitInv l r l' r' eK eL eR αL αR P
           hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply SpanPseudoCoconeHom.ext
    · exact iL.hom_inv_id
    · exact iR.hom_inv_id
  · apply SpanPseudoCoconeHom.ext
    · exact iL.inv_hom_id
    · exact iR.inv_hom_id

def unitNatIso {C : Type uC} [Category C] :
    𝟭 (SpanPseudoCocone l r C) ≅
      transportFunctor l r l' r' eK eL eR αL αR ⋙
        reverseTransportFunctor l r l' r' eK eL eR αL αR :=
  NatIso.ofComponents (unitIsoApp l r l' r' eK eL eR αL αR) (by
    intro P Q τ
    apply SpanPseudoCoconeHom.ext
    · exact (eL.congrLeft).unitIso.hom.naturality τ.left
    · exact (eR.congrLeft).unitIso.hom.naturality τ.right)

theorem left_counit_triangle {C : Type uC} [Category C] (F : L' ⥤ C) :
    (leftComparison l l' eK eL αL (eL.functor ⋙ F)).hom ≫
      Functor.whiskerLeft eK.inverse
        (reverseLeftComparison l l' eK eL αL F).inv ≫
      (eK.invFunIdAssoc (l' ⋙ F)).hom =
    Functor.whiskerLeft l' ((eL.congrLeft).counitIso.hom.app F) := by
  simpa only [leftComparison, reverseLeftComparison] using
    (spanRoundTripIso_counit eK eL l l' αL F)

theorem right_counit_triangle_inv {C : Type uC} [Category C] (F : R' ⥤ C) :
    (eK.invFunIdAssoc (r' ⋙ F)).inv ≫
      Functor.whiskerLeft eK.inverse
        (reverseRightComparison r r' eK eR αR F).hom ≫
      (rightComparison r r' eK eR αR (eR.functor ⋙ F)).inv =
    Functor.whiskerLeft r' ((eR.congrLeft).counitIso.inv.app F) := by
  simpa only [rightComparison, reverseRightComparison] using
    (spanRoundTripIso_counit_inv eK eR r r' αR F)

theorem right_counit_cancel {C : Type uC} [Category C] (F : R' ⥤ C) :
    (eK.invFunIdAssoc (r' ⋙ F)).inv ≫
      Functor.whiskerLeft eK.inverse
        (reverseRightComparison r r' eK eR αR F).hom ≫
      (rightComparison r r' eK eR αR (eR.functor ⋙ F)).inv ≫
      Functor.whiskerLeft r' ((eR.congrLeft).counitIso.hom.app F) = 𝟙 _ := by
  calc
    _ = Functor.whiskerLeft r' ((eR.congrLeft).counitIso.inv.app F) ≫
        Functor.whiskerLeft r' ((eR.congrLeft).counitIso.hom.app F) := by
      have h := reassoc_of% (right_counit_triangle_inv r r' eK eR αR F)
      simpa only [Category.assoc] using h
        (Functor.whiskerLeft r' ((eR.congrLeft).counitIso.hom.app F))
    _ = _ := (Functor.isoWhiskerLeft r'
      ((eR.congrLeft).counitIso.app F)).inv_hom_id

theorem middle_counit_conjugation {C : Type uC} [Category C]
    (Q : SpanPseudoCocone l' r' C) :
    Functor.whiskerLeft eK.inverse
        (Functor.isoWhiskerLeft eK.functor Q.glue).hom =
      (eK.invFunIdAssoc (l' ⋙ Q.left)).hom ≫ Q.glue.hom ≫
        (eK.invFunIdAssoc (r' ⋙ Q.right)).inv := by
  let oL := eK.invFunIdAssoc (l' ⋙ Q.left)
  let oR := eK.invFunIdAssoc (r' ⋙ Q.right)
  ext z
  have hz := Q.glue.hom.naturality (eK.counit.app z)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_mono (oR.hom.app z)).1
  calc
    _ = oL.hom.app z ≫ Q.glue.hom.app z := by
      simpa [oL, oR, Category.assoc] using hz.symm
    _ = (oL.hom.app z ≫ Q.glue.hom.app z ≫ oR.inv.app z) ≫
        oR.hom.app z := by
      symm
      simp only [Category.assoc, oR.inv_hom_id_app, Category.comp_id]

theorem whiskered_reverse_glue {C : Type uC} [Category C]
    (Q : SpanPseudoCocone l' r' C) :
    Functor.whiskerLeft eK.inverse
        (reverseTransportObj l r l' r' eK eL eR αL αR Q).glue.hom =
      Functor.whiskerLeft eK.inverse
          (reverseLeftComparison l l' eK eL αL Q.left).inv ≫
        Functor.whiskerLeft eK.inverse
          (Functor.isoWhiskerLeft eK.functor Q.glue).hom ≫
        Functor.whiskerLeft eK.inverse
          (reverseRightComparison r r' eK eR αR Q.right).hom := by
  simpa only [reverseTransportObj] using
    (whiskerLeft_three_comp_generic eK.inverse
      (reverseLeftComparison l l' eK eL αL Q.left).inv
      (Functor.isoWhiskerLeft eK.functor Q.glue).hom
      (reverseRightComparison r r' eK eR αR Q.right).hom)

theorem four_context_middle_substitution
    {A : Type*} [Category A] {X Y Z W V : A}
    (a : X ⟶ Y) (b b' : Y ⟶ Z) (c : Z ⟶ W) (d : W ⟶ V)
    (h : b = b') : (a ≫ b ≫ c) ≫ d = (a ≫ b' ≫ c) ≫ d := by
  rw [h]

theorem right_nested_substitution
    {A : Type*} [Category A] {X Y Z W V S T U : A}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (x : X ⟶ W)
    (m : W ⟶ V) (d : V ⟶ S) (e : S ⟶ T) (f : T ⟶ U)
    (g : U ⟶ V) (hp : a ≫ b ≫ c = x) (ht : d ≫ e ≫ f ≫ g = 𝟙 V) :
    (a ≫ (b ≫ (c ≫ m ≫ d) ≫ e) ≫ f) ≫ g = x ≫ m := by
  have h : ((a ≫ b ≫ c) ≫ m) ≫ (d ≫ e ≫ f ≫ g) = x ≫ m := by
    rw [hp, ht, Category.comp_id]
  simpa only [Category.assoc] using h

theorem counitGlueSquare {C : Type uC} [Category C]
    (Q : SpanPseudoCocone l' r' C) :
    (transportObj l r l' r' eK eL eR αL αR
      (reverseTransportObj l r l' r' eK eL eR αL αR Q)).glue.hom ≫
      Functor.whiskerLeft r' ((eR.congrLeft).counitIso.hom.app Q.right) =
    Functor.whiskerLeft l' ((eL.congrLeft).counitIso.hom.app Q.left) ≫
      Q.glue.hom := by
  let oL := eK.invFunIdAssoc (l' ⋙ Q.left)
  let oR := eK.invFunIdAssoc (r' ⋙ Q.right)
  have hW := whiskered_reverse_glue l r l' r' eK eL eR αL αR Q
  have hM := middle_counit_conjugation (eK := eK) (Q := Q)
  have hP := left_counit_triangle l l' eK eL αL Q.left
  have hT := right_counit_cancel r r' eK eR αR Q.right
  dsimp [transportObj]
  have hChain := congrArg
    (fun k => Functor.whiskerLeft eK.inverse
        (reverseLeftComparison l l' eK eL αL Q.left).inv ≫ k ≫
      Functor.whiskerLeft eK.inverse
        (reverseRightComparison r r' eK eR αR Q.right).hom) hM
  have hWG := hW.trans hChain
  refine (four_context_middle_substitution
    (leftComparison l l' eK eL αL (eL.functor ⋙ Q.left)).hom
    (Functor.whiskerLeft eK.inverse
      (reverseTransportObj l r l' r' eK eL eR αL αR Q).glue.hom)
    (Functor.whiskerLeft eK.inverse
        (reverseLeftComparison l l' eK eL αL Q.left).inv ≫
      (oL.hom ≫ Q.glue.hom ≫ oR.inv) ≫
      Functor.whiskerLeft eK.inverse
        (reverseRightComparison r r' eK eR αR Q.right).hom)
    (rightComparison r r' eK eR αR (eR.functor ⋙ Q.right)).inv
    (Functor.whiskerLeft r' ((eR.congrLeft).counitIso.hom.app Q.right))
    hWG).trans ?_
  exact right_nested_substitution
    (leftComparison l l' eK eL αL (eL.functor ⋙ Q.left)).hom
    (Functor.whiskerLeft eK.inverse
      (reverseLeftComparison l l' eK eL αL Q.left).inv)
    oL.hom
    (Functor.whiskerLeft l' ((eL.congrLeft).counitIso.hom.app Q.left))
    Q.glue.hom oR.inv
    (Functor.whiskerLeft eK.inverse
      (reverseRightComparison r r' eK eR αR Q.right).hom)
    (rightComparison r r' eK eR αR (eR.functor ⋙ Q.right)).inv
    (Functor.whiskerLeft r' ((eR.congrLeft).counitIso.hom.app Q.right))
    hP hT

def counitHom {C : Type uC} [Category C] (Q : SpanPseudoCocone l' r' C) :
    (reverseTransportFunctor l r l' r' eK eL eR αL αR ⋙
      transportFunctor l r l' r' eK eL eR αL αR).obj Q ⟶ Q where
  left := (eL.congrLeft).counitIso.hom.app Q.left
  right := (eR.congrLeft).counitIso.hom.app Q.right
  glue_naturality := counitGlueSquare l r l' r' eK eL eR αL αR Q

def counitInv {C : Type uC} [Category C] (Q : SpanPseudoCocone l' r' C) :
    Q ⟶ (reverseTransportFunctor l r l' r' eK eL eR αL αR ⋙
      transportFunctor l r l' r' eK eL eR αL αR).obj Q where
  left := (eL.congrLeft).counitIso.inv.app Q.left
  right := (eR.congrLeft).counitIso.inv.app Q.right
  glue_naturality := inverse_glue_square_of_forward
    (transportObj l r l' r' eK eL eR αL αR
      (reverseTransportObj l r l' r' eK eL eR αL αR Q)).glue.hom
    Q.glue.hom
    (Functor.isoWhiskerLeft l' ((eL.congrLeft).counitIso.app Q.left))
    (Functor.isoWhiskerLeft r' ((eR.congrLeft).counitIso.app Q.right))
    (counitGlueSquare l r l' r' eK eL eR αL αR Q)

def counitIsoApp {C : Type uC} [Category C] (Q : SpanPseudoCocone l' r' C) :
    (reverseTransportFunctor l r l' r' eK eL eR αL αR ⋙
      transportFunctor l r l' r' eK eL eR αL αR).obj Q ≅ Q := by
  let iL := (eL.congrLeft).counitIso.app Q.left
  let iR := (eR.congrLeft).counitIso.app Q.right
  refine { hom := counitHom l r l' r' eK eL eR αL αR Q
           inv := counitInv l r l' r' eK eL eR αL αR Q
           hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply SpanPseudoCoconeHom.ext
    · exact iL.hom_inv_id
    · exact iR.hom_inv_id
  · apply SpanPseudoCoconeHom.ext
    · exact iL.inv_hom_id
    · exact iR.inv_hom_id

def counitNatIso {C : Type uC} [Category C] :
    reverseTransportFunctor l r l' r' eK eL eR αL αR ⋙
        transportFunctor l r l' r' eK eL eR αL αR ≅
      Functor.id (SpanPseudoCocone l' r' C) :=
  NatIso.ofComponents (counitIsoApp l r l' r' eK eL eR αL αR) (by
    intro P Q τ
    apply SpanPseudoCoconeHom.ext
    · exact (eL.congrLeft).counitIso.hom.naturality τ.left
    · exact (eR.congrLeft).counitIso.hom.naturality τ.right)

theorem mapped_unit_comp_counit {C : Type uC} [Category C]
    (P : SpanPseudoCocone l r C) :
    (transportFunctor l r l' r' eK eL eR αL αR).map
          ((unitNatIso l r l' r' eK eL eR αL αR).hom.app P) ≫
        (counitNatIso l r l' r' eK eL eR αL αR).hom.app
          ((transportFunctor l r l' r' eK eL eR αL αR).obj P) =
      𝟙 ((transportFunctor l r l' r' eK eL eR αL αR).obj P) := by
  apply SpanPseudoCoconeHom.ext
  · exact (eL.congrLeft).functor_unitIso_comp P.left
  · exact (eR.congrLeft).functor_unitIso_comp P.right

/-- Transport through the three equivalences is an equivalence of the two
span-pseudococone categories. -/
def pseudoCoconeEquivalenceOfSpanEquivalences
    {C : Type uC} [Category C] :
    SpanPseudoCocone l r C ≌ SpanPseudoCocone l' r' C :=
  CategoryTheory.Equivalence.mk'
    (transportFunctor l r l' r' eK eL eR αL αR)
    (reverseTransportFunctor l r l' r' eK eL eR αL αR)
    (unitNatIso l r l' r' eK eL eR αL αR)
    (counitNatIso l r l' r' eK eL eR αL αR)
    (mapped_unit_comp_counit l r l' r' eK eL eR αL αR)

@[simp] theorem equivalence_functor
    {C : Type uC} [Category C] :
    (pseudoCoconeEquivalenceOfSpanEquivalences
      l r l' r' eK eL eR αL αR (C := C)).functor =
      transportFunctor l r l' r' eK eL eR αL αR := rfl

@[simp] theorem equivalence_inverse
    {C : Type uC} [Category C] :
    (pseudoCoconeEquivalenceOfSpanEquivalences
      l r l' r' eK eL eR αL αR (C := C)).inverse =
      reverseTransportFunctor l r l' r' eK eL eR αL αR := rfl

@[simp] theorem equivalence_unitIso_hom_app
    {C : Type uC} [Category C] (P : SpanPseudoCocone l r C) :
    (pseudoCoconeEquivalenceOfSpanEquivalences
      l r l' r' eK eL eR αL αR).unitIso.hom.app P =
      (unitNatIso l r l' r' eK eL eR αL αR).hom.app P := rfl

@[simp] theorem equivalence_counitIso_hom_app
    {C : Type uC} [Category C] (Q : SpanPseudoCocone l' r' C) :
    (pseudoCoconeEquivalenceOfSpanEquivalences
      l r l' r' eK eL eR αL αR).counitIso.hom.app Q =
      (counitNatIso l r l' r' eK eL eR αL αR).hom.app Q := rfl

def reverseTransportPostcomposeIsoApp {C : Type uC} {D : Type uD}
    [Category C] [Category D] (H : Functor C D) (Q : SpanPseudoCocone l' r' C) :
    (reverseTransportFunctor l r l' r' eK eL eR αL αR (C := D)).obj
        ((postcomposeFunctor H).obj Q) ≅
      (postcomposeFunctor H).obj
        ((reverseTransportFunctor l r l' r' eK eL eR αL αR
          (C := C)).obj Q) := by
  let aL := Functor.associator eL.functor Q.left H
  let aR := Functor.associator eR.functor Q.right H
  refine { hom := { left := aL.hom, right := aR.hom, glue_naturality := ?_ }
           inv := { left := aL.inv, right := aR.inv, glue_naturality := ?_ }
           hom_inv_id := ?_, inv_hom_id := ?_ }
  · ext z
    simp [reverseTransportFunctor, reverseTransportObj, postcomposeFunctor,
      postcomposeObj, reverseLeftComparison, reverseRightComparison, aL, aR]
  · ext z
    simp [reverseTransportFunctor, reverseTransportObj, postcomposeFunctor,
      postcomposeObj, reverseLeftComparison, reverseRightComparison, aL, aR]
  · apply SpanPseudoCoconeHom.ext
    · exact aL.hom_inv_id
    · exact aR.hom_inv_id
  · apply SpanPseudoCoconeHom.ext
    · exact aL.inv_hom_id
    · exact aR.inv_hom_id

def reverseTransportPostcomposeIso {C : Type uC} {D : Type uD}
    [Category C] [Category D] (H : Functor C D) :
    postcomposeFunctor H ⋙
        reverseTransportFunctor l r l' r' eK eL eR αL αR (C := D) ≅
      reverseTransportFunctor l r l' r' eK eL eR αL αR (C := C) ⋙
        postcomposeFunctor H :=
  NatIso.ofComponents
    (reverseTransportPostcomposeIsoApp l r l' r' eK eL eR αL αR H) (by
      intro P Q τ
      apply SpanPseudoCoconeHom.ext
      · ext z
        change H.map (τ.left.app (eL.functor.obj z)) ≫ 𝟙 _ =
          𝟙 _ ≫ H.map (τ.left.app (eL.functor.obj z))
        simp
      · ext z
        change H.map (τ.right.app (eR.functor.obj z)) ≫ 𝟙 _ =
          𝟙 _ ≫ H.map (τ.right.app (eR.functor.obj z))
        simp)

def equivalenceFunctorPostcomposeIso {C : Type uC} {D : Type uD}
    [Category C] [Category D] (H : Functor C D) :
    postcomposeFunctor H ⋙
        (pseudoCoconeEquivalenceOfSpanEquivalences
          l r l' r' eK eL eR αL αR (C := D)).functor ≅
      (pseudoCoconeEquivalenceOfSpanEquivalences
          l r l' r' eK eL eR αL αR (C := C)).functor ⋙
        postcomposeFunctor H :=
  transportPostcomposeIso l r l' r' eK eL eR αL αR H

def equivalenceInversePostcomposeIso {C : Type uC} {D : Type uD}
    [Category C] [Category D] (H : Functor C D) :
    postcomposeFunctor H ⋙
        (pseudoCoconeEquivalenceOfSpanEquivalences
          l r l' r' eK eL eR αL αR (C := D)).inverse ≅
      (pseudoCoconeEquivalenceOfSpanEquivalences
          l r l' r' eK eL eR αL αR (C := C)).inverse ⋙
        postcomposeFunctor H :=
  reverseTransportPostcomposeIso l r l' r' eK eL eR αL αR H

@[simp] theorem equivalenceFunctorPostcomposeIso_app_left
    {C : Type uC} {D : Type uD} [Category C] [Category D]
    (H : Functor C D) (P : SpanPseudoCocone l r C) :
    ((equivalenceFunctorPostcomposeIso
      l r l' r' eK eL eR αL αR H).hom.app P).left =
      (Functor.associator eL.inverse P.left H).hom := rfl

@[simp] theorem equivalenceInversePostcomposeIso_app_left
    {C : Type uC} {D : Type uD} [Category C] [Category D]
    (H : Functor C D) (Q : SpanPseudoCocone l' r' C) :
    ((equivalenceInversePostcomposeIso
      l r l' r' eK eL eR αL αR H).hom.app Q).left =
      (Functor.associator eL.functor Q.left H).hom := rfl


#print axioms spanRoundTripIso_unit_inv_with_prefix
#print axioms inverse_glue_square_of_forward
#print axioms unitGlueSquare
#print axioms unitHom
#print axioms unitInv
#print axioms unitIsoApp
#print axioms unitNatIso
#print axioms counitGlueSquare
#print axioms counitNatIso
#print axioms mapped_unit_comp_counit
#print axioms pseudoCoconeEquivalenceOfSpanEquivalences
#print axioms reverseTransportPostcomposeIso
#print axioms equivalenceFunctorPostcomposeIso
#print axioms equivalenceInversePostcomposeIso

end ConstructionTargets.GenericSpanPseudoCoconeTransport
