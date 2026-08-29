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
variable {C : Type*} [Category C]

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

#print axioms twoOpenFundamentalGroupoidPseudopushoutEquivalence
#print axioms pseudopushoutEquivalence_functor_obj_left
#print axioms pseudopushoutEquivalence_functor_obj_right
#print axioms pseudopushoutEquivalence_functor_obj_glue
#print axioms pseudopushoutEquivalence_functor_map_left
#print axioms pseudopushoutEquivalence_functor_map_right
#print axioms twoOpenFundamentalGroupoid_pseudopushout_mapping_property

end ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
