import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.TwoOpenPointSpanComparison
import ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
import ConstructionTargets.FreeProductRepresentationSingleObjEquivalence
noncomputable section
open CategoryTheory
namespace ConstructionTargets.TwoOpenFreeProductMapping
open TwoOpenFundamentalGroupoidSpan TwoOpenFundamentalGroupoidPseudopushout
open GenericSpanPseudoCoconeTransport FreeProductPointSpanRepresentations
open FreeProductRepresentationSingleObjEquivalence TwoOpenLegCompatibleConnectorSystems
variable {X : Type} [TopologicalSpace X] {U V : Set X}
variable (C : Type) [Category C]
def pseudoToSpanObj
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :
    SpanPseudoCocone (overlapFundamentalGroupoidMap (U := U) (V := V) true) (overlapFundamentalGroupoidMap (U := U) (V := V) false) C where
  left := P.left
  right := P.right
  glue := P.glue

def pseudoToSpanMap
    {P Q : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)}
    (f : P ⟶ Q) : pseudoToSpanObj (U := U) (V := V) C P ⟶ pseudoToSpanObj (U := U) (V := V) C Q where
  left := f.left
  right := f.right
  glue_naturality := f.glue_naturality

def pseudoToSpanFunctor :
    PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C) ⥤
      SpanPseudoCocone (overlapFundamentalGroupoidMap (U := U) (V := V) true) (overlapFundamentalGroupoidMap (U := U) (V := V) false) C where
  obj := pseudoToSpanObj (U := U) (V := V) C
  map := pseudoToSpanMap (U := U) (V := V) C
  map_id _ := rfl
  map_comp _ _ := rfl

def spanToPseudoObj (P : SpanPseudoCocone (overlapFundamentalGroupoidMap (U := U) (V := V) true) (overlapFundamentalGroupoidMap (U := U) (V := V) false) C) :
    PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C) where
  left := P.left
  right := P.right
  glue := P.glue

def spanToPseudoMap {P Q : SpanPseudoCocone (overlapFundamentalGroupoidMap (U := U) (V := V) true) (overlapFundamentalGroupoidMap (U := U) (V := V) false) C} (f : P ⟶ Q) :
    spanToPseudoObj (U := U) (V := V) C P ⟶ spanToPseudoObj (U := U) (V := V) C Q where
  left := f.left
  right := f.right
  glue_naturality := f.glue_naturality

def spanToPseudoFunctor :
    SpanPseudoCocone (overlapFundamentalGroupoidMap (U := U) (V := V) true) (overlapFundamentalGroupoidMap (U := U) (V := V) false) C ⥤
      PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C) where
  obj := spanToPseudoObj (U := U) (V := V) C
  map := spanToPseudoMap (U := U) (V := V) C
  map_id _ := rfl
  map_comp _ _ := rfl

def pseudoSpanEquivalence :
    PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C) ≌
      SpanPseudoCocone (overlapFundamentalGroupoidMap (U := U) (V := V) true) (overlapFundamentalGroupoidMap (U := U) (V := V) false) C where
  functor := pseudoToSpanFunctor (U := U) (V := V) C
  inverse := spanToPseudoFunctor (U := U) (V := V) C
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


variable [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace (U ∩ V : Set X)]
variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (w : (U ∩ V : Set X))
def mapping :
    (FundamentalGroupoid X ⥤ C) ≌
      (SingleObj (Monoid.Coprod (End (leftConnectors w).base) (End (rightConnectors w).base)) ⥤ C) :=
  (((twoOpenFundamentalGroupoidPseudopushoutEquivalence (C := C) hU hV hcover).trans
    (pseudoSpanEquivalence (U := U) (V := V) C)).trans
    (TwoOpenPointSpanComparison.comparison U V w C)).trans
    ((freeProductPointSpanEquivalence (C := C) (End (leftConnectors w).base) (End (rightConnectors w).base)).trans
      (representationSingleObjEquivalence (C := C) (End (leftConnectors w).base) (End (rightConnectors w).base)))
def postcomposeIso {D : Type} [Category D] (K : C ⥤ D) :
    (Functor.whiskeringRight (FundamentalGroupoid X) C D).obj K ⋙ (mapping D hU hV hcover w).functor ≅
      (mapping C hU hV hcover w).functor ⋙
        (Functor.whiskeringRight (SingleObj (Monoid.Coprod (End (leftConnectors w).base)
          (End (rightConnectors w).base))) C D).obj K := by
  let s0 : CatCommSq _
      (twoOpenFundamentalGroupoidPseudopushoutEquivalence (C := C) hU hV hcover).functor
      (twoOpenFundamentalGroupoidPseudopushoutEquivalence (C := D) hU hV hcover).functor
      (postcomposePseudoFunctorCoconeFunctor K) :=
    ⟨pseudopushoutPostcomposeNatIso hU hV hcover K⟩
  let s1 : CatCommSq (postcomposePseudoFunctorCoconeFunctor K)
      (pseudoSpanEquivalence (U := U) (V := V) C).functor
      (pseudoSpanEquivalence (U := U) (V := V) D).functor (postcomposeFunctor K) :=
    ⟨eqToIso (by rfl)⟩
  let s2 : CatCommSq (postcomposeFunctor K)
      (TwoOpenPointSpanComparison.comparison U V w C).functor
      (TwoOpenPointSpanComparison.comparison U V w D).functor (postcomposeFunctor K) :=
    ⟨TwoOpenPointSpanComparison.postcomposeIso U V w K⟩
  let s3 : CatCommSq (postcomposeFunctor K)
      (freeProductPointSpanEquivalence (End (leftConnectors w).base) (End (rightConnectors w).base) C).functor
      (freeProductPointSpanEquivalence (End (leftConnectors w).base) (End (rightConnectors w).base) D).functor
      (FreeProductPointSpanRepresentations.postcomposeRepresentationFunctor
        (End (leftConnectors w).base) (End (rightConnectors w).base) K) :=
    ⟨FreeProductPointSpanRepresentations.equivalenceFunctorPostcomposeIso
      (End (leftConnectors w).base) (End (rightConnectors w).base) K⟩
  let s4 : CatCommSq
      (FreeProductPointSpanRepresentations.postcomposeRepresentationFunctor
        (End (leftConnectors w).base) (End (rightConnectors w).base) K)
      (representationSingleObjEquivalence (C := C) (End (leftConnectors w).base) (End (rightConnectors w).base)).functor
      (representationSingleObjEquivalence (C := D) (End (leftConnectors w).base) (End (rightConnectors w).base)).functor _ :=
    ⟨representationToFunctorPostcomposeIso (End (leftConnectors w).base) (End (rightConnectors w).base) K⟩
  exact (CatCommSq.vComp' (CatCommSq.vComp' (CatCommSq.vComp' s0 s1) s2) (CatCommSq.vComp' s3 s4)).iso
def sourceEquivalence : FundamentalGroupoid X ≌
    SingleObj (Monoid.Coprod (End (leftConnectors w).base) (End (rightConnectors w).base)) :=
  GenericTargetNaturalSourceReconstruction.sourceEquivalence
    (fun C _ => mapping C hU hV hcover w) (fun K => postcomposeIso _ hU hV hcover w K)

def groupEquivalence : FundamentalGroup X w.val ≃*
    Monoid.Coprod (FundamentalGroup U ⟨w.val,w.property.1⟩)
      (FundamentalGroup V ⟨w.val,w.property.2⟩) :=
  ((sourceEquivalence hU hV hcover w).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk w.val)).trans
    ((Iso.conj (eqToIso (show (sourceEquivalence hU hV hcover w).functor.obj (FundamentalGroupoid.mk w.val) =
      SingleObj.star (Monoid.Coprod (End (leftConnectors w).base) (End (rightConnectors w).base)) from
      Subsingleton.elim _ _))).trans (SingleObj.toEnd _).symm)

def basedGroupEquivalence (u : U) (v : V)
    (p : Path (⟨w.val,w.property.1⟩ : U) u) (q : Path (⟨w.val,w.property.2⟩ : V) v) :
    FundamentalGroup X w.val ≃* Monoid.Coprod (FundamentalGroup U u) (FundamentalGroup V v) :=
  (groupEquivalence hU hV hcover w).trans
    (MulEquiv.coprodCongr (FundamentalGroup.fundamentalGroupMulEquivOfPath p) (FundamentalGroup.fundamentalGroupMulEquivOfPath q))

def chosenGroupEquivalence (u : U) (v : V) :
    FundamentalGroup X w.val ≃* Monoid.Coprod (FundamentalGroup U u) (FundamentalGroup V v) :=
  basedGroupEquivalence hU hV hcover w u v (PathConnectedSpace.somePath _ _) (PathConnectedSpace.somePath _ _)
#print axioms sourceEquivalence
#print axioms groupEquivalence
#print axioms basedGroupEquivalence
#print axioms chosenGroupEquivalence
#print axioms postcomposeIso
#print axioms pseudoSpanEquivalence
#print axioms mapping
end ConstructionTargets.TwoOpenFreeProductMapping
