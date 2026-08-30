import ConstructionTargets.TwoOpenPseudoCoconeStrictification

/-!
# The two-open fundamental-groupoid pseudopushout mapping property

This file composes descent reconstruction with pseudococone strictification.
The result is deliberately stated as an equivalence with pseudococones, not
as an ordinary `Limits.Pushout` assertion.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.TwoOpenDescentCategory
open ConstructionTargets.TwoOpenDescentRestriction
open ConstructionTargets.TwoOpenDescentReconstruction
open ConstructionTargets.TwoOpenFundamentalGroupoidSpan
open ConstructionTargets.TwoOpenPseudoCoconeStrictification

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C D : Type*} [Category C] [Category D]

/-- Functors from the ambient fundamental groupoid are equivalent to
pseudococones of functors from the two cover pieces. -/
def twoOpenFundamentalGroupoidPseudopushoutEquivalence
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    (FundamentalGroupoid X ⥤ C) ≌
      PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C) :=
  (twoOpenDescentEquivalence (C := C) hU hV hcover).trans
    (twoOpenDescentPseudoCoconeEquivalence (C := C) hcover)

/-- The left component of the forward pseudococone is literal restriction
along the left cover inclusion. -/
@[simp] theorem pseudopushoutEquivalence_functor_obj_left
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (F : FundamentalGroupoid X ⥤ C) :
    ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C) hU hV hcover).functor.obj F).left =
      FundamentalGroupoid.map (coverPieceInclusion true) ⋙ F := rfl

/-- The right component of the forward pseudococone is literal restriction
along the right cover inclusion. -/
@[simp] theorem pseudopushoutEquivalence_functor_obj_right
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (F : FundamentalGroupoid X ⥤ C) :
    ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C) hU hV hcover).functor.obj F).right =
      FundamentalGroupoid.map (coverPieceInclusion false) ⋙ F := rfl

/-- The overlap 2-cell of the forward pseudococone is the canonical descent
overlap isomorphism for the restricted ambient functor. -/
@[simp] theorem pseudopushoutEquivalence_functor_obj_glue
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (F : FundamentalGroupoid X ⥤ C) :
    ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C) hU hV hcover).functor.obj F).glue =
      descentOverlapIso
        (canonicalTwoOpenDescentDatum (U := U) (V := V) F) := rfl

/-- On morphisms, the forward equivalence is restriction/whiskering on the
left piece. -/
@[simp] theorem pseudopushoutEquivalence_functor_map_left
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {F G : FundamentalGroupoid X ⥤ C} (tau : F ⟶ G) :
    ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C) hU hV hcover).functor.map tau).left =
      Functor.whiskerLeft (FundamentalGroupoid.map (coverPieceInclusion true)) tau := rfl

/-- On morphisms, the forward equivalence is restriction/whiskering on the
right piece. -/
@[simp] theorem pseudopushoutEquivalence_functor_map_right
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    {F G : FundamentalGroupoid X ⥤ C} (tau : F ⟶ G) :
    ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
      (C := C) hU hV hcover).functor.map tau).right =
      Functor.whiskerLeft (FundamentalGroupoid.map (coverPieceInclusion false)) tau := rfl

/-- Named interface for the two-open pseudopushout mapping property.  Its
content is an equivalence of mapping categories with pseudococones, for an
arbitrary target category `C`. -/
theorem twoOpenFundamentalGroupoid_pseudopushout_mapping_property
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Nonempty ((FundamentalGroupoid X ⥤ C) ≌
      PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :=
  ⟨twoOpenFundamentalGroupoidPseudopushoutEquivalence
    (C := C) hU hV hcover⟩

/-- The forward pseudopushout equivalence commutes with target
postcomposition, objectwise, up to the inverse associators on the two legs. -/
def pseudopushoutPostcomposeComparisonApp
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (H : C ⥤ D) (F : FundamentalGroupoid X ⥤ C) :
    ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
        (C := D) hU hV hcover).functor.obj (F ⋙ H)) ≅
      postcomposePseudoFunctorCoconeObj H
        ((twoOpenFundamentalGroupoidPseudopushoutEquivalence
          (C := C) hU hV hcover).functor.obj F) := by
  let l :
      (((FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) true) ⋙ F) ⋙ H) ≅
        (FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) true) ⋙ (F ⋙ H))) :=
    Functor.associator _ _ _
  let r :
      (((FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) false) ⋙ F) ⋙ H) ≅
        (FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) false) ⋙ (F ⋙ H))) :=
    Functor.associator _ _ _
  refine { hom := { left := l.inv, right := r.inv, glue_naturality := ?_ },
            inv := { left := l.hom, right := r.hom, glue_naturality := ?_ },
            hom_inv_id := ?_, inv_hom_id := ?_ }
  · ext z
    simp [postcomposePseudoFunctorCoconeObj, l, r,
      descentOverlapIso, descentOverlapAppIso, functor_map_eqToHom]
  · ext z
    simp [postcomposePseudoFunctorCoconeObj, l, r,
      descentOverlapIso, descentOverlapAppIso, functor_map_eqToHom]
  · apply PseudoFunctorCoconeHom.ext
    · ext z
      change l.inv.app z ≫ l.hom.app z = 𝟙 _
      exact l.inv_hom_id_app z
    · ext z
      change r.inv.app z ≫ r.hom.app z = 𝟙 _
      exact r.inv_hom_id_app z
  · apply PseudoFunctorCoconeHom.ext
    · ext z
      change l.hom.app z ≫ l.inv.app z = 𝟙 _
      exact l.hom_inv_id_app z
    · ext z
      change r.hom.app z ≫ r.inv.app z = 𝟙 _
      exact r.hom_inv_id_app z

/-- Target postcomposition is pseudonatural for the forward two-open
fundamental-groupoid pseudopushout equivalence. -/
def pseudopushoutPostcomposeNatIso
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (H : C ⥤ D) :
    (Functor.whiskeringRight (FundamentalGroupoid X) C D).obj H ⋙
        (twoOpenFundamentalGroupoidPseudopushoutEquivalence
          (C := D) hU hV hcover).functor ≅
      (twoOpenFundamentalGroupoidPseudopushoutEquivalence
          (C := C) hU hV hcover).functor ⋙
        postcomposePseudoFunctorCoconeFunctor H :=
  NatIso.ofComponents
    (pseudopushoutPostcomposeComparisonApp hU hV hcover H)
    (by
      intro F G tau
      apply PseudoFunctorCoconeHom.ext
      · ext z
        change H.map (tau.app _) ≫ 𝟙 _ = 𝟙 _ ≫ H.map (tau.app _)
        simp
      · ext z
        change H.map (tau.app _) ≫ 𝟙 _ = 𝟙 _ ≫ H.map (tau.app _)
        simp)

#print axioms twoOpenFundamentalGroupoidPseudopushoutEquivalence
#print axioms pseudopushoutEquivalence_functor_obj_left
#print axioms pseudopushoutEquivalence_functor_obj_right
#print axioms pseudopushoutEquivalence_functor_obj_glue
#print axioms pseudopushoutEquivalence_functor_map_left
#print axioms pseudopushoutEquivalence_functor_map_right
#print axioms twoOpenFundamentalGroupoid_pseudopushout_mapping_property
#print axioms pseudopushoutPostcomposeComparisonApp
#print axioms pseudopushoutPostcomposeNatIso

end ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
