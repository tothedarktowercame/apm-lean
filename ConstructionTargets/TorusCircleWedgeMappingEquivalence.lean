import ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
import ConstructionTargets.TorusCircleWedgeFreeProductComposite
import ConstructionTargets.FreeProductRepresentationSingleObjEquivalence

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TorusCircleWedgeMappingEquivalence

open ConstructionTargets.TwoOpenFundamentalGroupoidSpan
open ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
open ConstructionTargets.GenericSpanPseudoCoconeTransport
open ConstructionTargets.TorusCircleWedgeOpenCover
open ConstructionTargets.TorusCircleWedgeFundamentalGroupoidSpan
open ConstructionTargets.TorusCircleWedgeFreeProductComposite
open ConstructionTargets.FreeProductRepresentationSingleObjEquivalence
open ConstructionTargets.FreeProductPointSpanRepresentations

abbrev G₁ := Multiplicative (ℤ × ℤ)
abbrev G₂ := Multiplicative ℤ
abbrev FP := Monoid.Coprod G₁ G₂

variable (C : Type) [Category C]

def pseudoToSpanObj
    (P : PseudoFunctorCocone (X := GenericWedge) (U := U) (V := V) (C := C)) :
    SpanPseudoCocone actualLeft actualRight C where
  left := P.left
  right := P.right
  glue := P.glue

def pseudoToSpanMap
    {P Q : PseudoFunctorCocone (X := GenericWedge) (U := U) (V := V) (C := C)}
    (f : P ⟶ Q) : pseudoToSpanObj C P ⟶ pseudoToSpanObj C Q where
  left := f.left
  right := f.right
  glue_naturality := f.glue_naturality

def pseudoToSpanFunctor :
    PseudoFunctorCocone (X := GenericWedge) (U := U) (V := V) (C := C) ⥤
      SpanPseudoCocone actualLeft actualRight C where
  obj := pseudoToSpanObj C
  map := pseudoToSpanMap C
  map_id _ := rfl
  map_comp _ _ := rfl

def spanToPseudoObj (P : SpanPseudoCocone actualLeft actualRight C) :
    PseudoFunctorCocone (X := GenericWedge) (U := U) (V := V) (C := C) where
  left := P.left
  right := P.right
  glue := P.glue

def spanToPseudoMap {P Q : SpanPseudoCocone actualLeft actualRight C} (f : P ⟶ Q) :
    spanToPseudoObj C P ⟶ spanToPseudoObj C Q where
  left := f.left
  right := f.right
  glue_naturality := f.glue_naturality

def spanToPseudoFunctor :
    SpanPseudoCocone actualLeft actualRight C ⥤
      PseudoFunctorCocone (X := GenericWedge) (U := U) (V := V) (C := C) where
  obj := spanToPseudoObj C
  map := spanToPseudoMap C
  map_id _ := rfl
  map_comp _ _ := rfl

def pseudoSpanEquivalence :
    PseudoFunctorCocone (X := GenericWedge) (U := U) (V := V) (C := C) ≌
      SpanPseudoCocone actualLeft actualRight C where
  functor := pseudoToSpanFunctor C
  inverse := spanToPseudoFunctor C
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply PseudoFunctorCoconeHom.ext
    · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
    · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right; simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply SpanPseudoCoconeHom.ext
    · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
    · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right; simp)
  functor_unitIso_comp X := by
    apply SpanPseudoCoconeHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp

def genericWedgeFreeProductMappingEquivalence :
    (FundamentalGroupoid GenericWedge ⥤ C) ≌
      ConstructionTargets.FreeProductPointSpanRepresentations.FreeProductRepresentation
        (C := C) G₁ G₂ :=
  ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
    (C := C) U_isOpen V_isOpen U_union_V).trans
      (pseudoSpanEquivalence C)).trans (actualToFreeProductEquivalence C)

def genericWedgeSingleObjMappingEquivalence :
    (FundamentalGroupoid GenericWedge ⥤ C) ≌ (SingleObj FP ⥤ C) :=
  (genericWedgeFreeProductMappingEquivalence C).trans
    (representationSingleObjEquivalence (C := C) G₁ G₂)

#print axioms pseudoSpanEquivalence
#print axioms genericWedgeSingleObjMappingEquivalence

end ConstructionTargets.TorusCircleWedgeMappingEquivalence
