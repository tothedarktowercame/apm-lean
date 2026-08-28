import ConstructionTargets.TwoOpenDescentRestriction

/-!
# Uniqueness for two-open fundamental-groupoid descent

This file proves the faithful (uniqueness-of-2-cells) part of the two-open
descent universal property.  Natural transformations between ambient
fundamental-groupoid functors are determined by their restrictions to the two
cover pieces.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenDescentUniqueness

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.TwoOpenDescentRestriction

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- Agreement after restriction to both members of a two-open cover determines
an ambient natural transformation.  This is the faithful part of the descent
universal property; unlike the construction of an ambient functor, it is an
objectwise statement and therefore does not require choosing subdivisions. -/
theorem natTrans_ext_of_twoOpen_restrictions
    (hcover : U ∪ V = Set.univ)
    {F G : FundamentalGroupoid X ⥤ C} (α β : F ⟶ G)
    (hU : Functor.whiskerLeft
        (FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) true)) α =
      Functor.whiskerLeft
        (FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) true)) β)
    (hV : Functor.whiskerLeft
        (FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) false)) α =
      Functor.whiskerLeft
        (FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) false)) β) :
    α = β := by
  ext x
  have hx : x.as ∈ U ∪ V := by rw [hcover]; trivial
  rcases hx with hxU | hxV
  · have h := NatTrans.congr_app hU
      (show FundamentalGroupoid (CoverPiece U V true) from ⟨⟨x.as, hxU⟩⟩)
    exact h
  · have h := NatTrans.congr_app hV
      (show FundamentalGroupoid (CoverPiece U V false) from ⟨⟨x.as, hxV⟩⟩)
    exact h

/-- A componentwise version convenient when restriction equalities have
already been evaluated at cover-piece objects. -/
theorem natTrans_ext_of_twoOpen_app
    (hcover : U ∪ V = Set.univ)
    {F G : FundamentalGroupoid X ⥤ C} (α β : F ⟶ G)
    (hU : ∀ z : FundamentalGroupoid (CoverPiece U V true),
      α.app ((FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) true)).obj z) =
        β.app ((FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) true)).obj z))
    (hV : ∀ z : FundamentalGroupoid (CoverPiece U V false),
      α.app ((FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) false)).obj z) =
        β.app ((FundamentalGroupoid.map (coverPieceInclusion (U := U) (V := V) false)).obj z)) :
    α = β := by
  ext x
  have hx : x.as ∈ U ∪ V := by rw [hcover]; trivial
  rcases hx with hxU | hxV
  · exact hU ⟨⟨x.as, hxU⟩⟩
  · exact hV ⟨⟨x.as, hxV⟩⟩

#print axioms natTrans_ext_of_twoOpen_restrictions
#print axioms natTrans_ext_of_twoOpen_app

end ConstructionTargets.TwoOpenDescentUniqueness
