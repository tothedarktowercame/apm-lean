import ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
import ConstructionTargets.TorusCircleWedgeFreeProductComposite
import ConstructionTargets.FreeProductRepresentationSingleObjEquivalence
import Mathlib.CategoryTheory.CatCommSq

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

variable {C D : Type} [Category C] [Category D]

abbrev spanPostcomposeRepresentation (K : C ⥤ D) :=
  ConstructionTargets.FreeProductPointSpanRepresentations.postcomposeRepresentationFunctor
    G₁ G₂ K

abbrev singleObjPostcomposeRepresentation (K : C ⥤ D) :=
  ConstructionTargets.FreeProductRepresentationSingleObjEquivalence.postcomposeRepresentationFunctor
    G₁ G₂ K

def postcomposeRepresentationAlignmentApp (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G₁ G₂) :
    (spanPostcomposeRepresentation K).obj R ≅
      (singleObjPostcomposeRepresentation K).obj R where
  hom := ⟨𝟙 _, by
    intro x
    change mappedAction G₁ G₂ K R x ≫ 𝟙 _ =
      𝟙 _ ≫ mappedAction G₁ G₂ K R x
    simp⟩
  inv := ⟨𝟙 _, by
    intro x
    change mappedAction G₁ G₂ K R x ≫ 𝟙 _ =
      𝟙 _ ≫ mappedAction G₁ G₂ K R x
    simp⟩
  hom_inv_id := by apply FreeProductRepresentationHom.ext; exact Category.id_comp _
  inv_hom_id := by apply FreeProductRepresentationHom.ext; exact Category.id_comp _

def postcomposeRepresentationAlignment (K : C ⥤ D) :
    spanPostcomposeRepresentation K ≅ singleObjPostcomposeRepresentation K :=
  NatIso.ofComponents (postcomposeRepresentationAlignmentApp K) (by
    intro R S f
    apply FreeProductRepresentationHom.ext
    change K.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ K.map f.hom
    simp)

def pseudoSpanPostcomposeIso (K : C ⥤ D) :
    postcomposePseudoFunctorCoconeFunctor K ⋙ pseudoToSpanFunctor D ≅
      pseudoToSpanFunctor C ⋙ postcomposeFunctor K :=
  eqToIso (by rfl)

@[reducible] def openCoverSquare (K : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (FundamentalGroupoid GenericWedge) C D).obj K)
    (twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C) U_isOpen V_isOpen U_union_V).functor
    (twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := D) U_isOpen V_isOpen U_union_V).functor
    (postcomposePseudoFunctorCoconeFunctor K) where
  iso := pseudopushoutPostcomposeNatIso U_isOpen V_isOpen U_union_V K

@[reducible] def pseudoSpanSquare (K : C ⥤ D) : CatCommSq
    (postcomposePseudoFunctorCoconeFunctor K)
    (pseudoSpanEquivalence C).functor (pseudoSpanEquivalence D).functor
    (postcomposeFunctor K) where
  iso := pseudoSpanPostcomposeIso K

@[reducible] def mappingToSpanRepresentationSquare (K : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (FundamentalGroupoid GenericWedge) C D).obj K)
    (genericWedgeFreeProductMappingEquivalence C).functor
    (genericWedgeFreeProductMappingEquivalence D).functor
    (spanPostcomposeRepresentation K) :=
  CatCommSq.vComp'
    (CatCommSq.vComp' (openCoverSquare K) (pseudoSpanSquare K))
    (actualFreeProductSquare K)

@[reducible] def alignmentSquare (K : C ⥤ D) : CatCommSq
    (spanPostcomposeRepresentation K)
    (𝟭 (FreeProductRepresentation (C := C) G₁ G₂))
    (𝟭 (FreeProductRepresentation (C := D) G₁ G₂))
    (singleObjPostcomposeRepresentation K) where
  iso := (Functor.rightUnitor _).trans
    ((postcomposeRepresentationAlignment K).trans (Functor.leftUnitor _).symm)

@[reducible] def alignedMappingSquare (K : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (FundamentalGroupoid GenericWedge) C D).obj K)
    (genericWedgeFreeProductMappingEquivalence C).functor
    (genericWedgeFreeProductMappingEquivalence D).functor
    (singleObjPostcomposeRepresentation K) where
  iso := (mappingToSpanRepresentationSquare K).iso.trans
    (Functor.isoWhiskerLeft
      (genericWedgeFreeProductMappingEquivalence C).functor
      (postcomposeRepresentationAlignment K))

@[reducible] def representationSingleObjSquare (K : C ⥤ D) : CatCommSq
    (singleObjPostcomposeRepresentation K)
    (representationSingleObjEquivalence (C := C) G₁ G₂).functor
    (representationSingleObjEquivalence (C := D) G₁ G₂).functor
    ((Functor.whiskeringRight (SingleObj FP) C D).obj K) where
  iso := representationToFunctorPostcomposeIso G₁ G₂ K

@[reducible] def genericWedgeSingleObjSquare (K : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight (FundamentalGroupoid GenericWedge) C D).obj K)
    (genericWedgeSingleObjMappingEquivalence C).functor
    (genericWedgeSingleObjMappingEquivalence D).functor
    ((Functor.whiskeringRight (SingleObj FP) C D).obj K) :=
  CatCommSq.vComp'
    (alignedMappingSquare K)
    (representationSingleObjSquare K)

def genericWedgeSingleObjPostcomposeIso (K : C ⥤ D) :=
  (genericWedgeSingleObjSquare K).iso

@[simp] theorem alignment_hom_app_hom (K : C ⥤ D)
    (R : FreeProductRepresentation (C := C) G₁ G₂) :
    ((postcomposeRepresentationAlignment K).hom.app R).hom = 𝟙 _ := rfl

#print axioms postcomposeRepresentationAlignment
#print axioms genericWedgeSingleObjPostcomposeIso
#print axioms pseudoSpanEquivalence
#print axioms genericWedgeSingleObjMappingEquivalence

end ConstructionTargets.TorusCircleWedgeMappingEquivalence
