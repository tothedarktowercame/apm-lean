import ConstructionTargets.TwoOpenDescentCategory

/-!
# The two-open fundamental-groupoid span
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenFundamentalGroupoidSpan

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.TwoOpenDescentRestriction

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- The intersection, retaining both membership proofs. -/
abbrev CoverOverlap := {x : X // x ∈ U ∧ x ∈ V}

/-- Inclusion of the overlap into either cover piece.  `true` is `U` and
`false` is `V`, following `twoChart`. -/
def overlapToPiece : (b : Bool) →
    C(CoverOverlap (X := X) (U := U) (V := V), CoverPiece U V b)
  | false => ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩
  | true => ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- Inclusion of the overlap directly into the ambient space. -/
def overlapInclusion : C(CoverOverlap (X := X) (U := U) (V := V), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem overlap_piece_ambient_comp (b : Bool) :
    (coverPieceInclusion (U := U) (V := V) b).comp (overlapToPiece b) =
      overlapInclusion := by
  cases b
  apply ContinuousMap.ext
  intro x
  rfl
  apply ContinuousMap.ext
  intro x
  rfl

/-- The two legs of the span of fundamental groupoids. -/
def overlapFundamentalGroupoidMap (b : Bool) :
    FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V)) ⥤
      FundamentalGroupoid (CoverPiece U V b) :=
  FundamentalGroupoid.map (overlapToPiece b)

/-- The two inclusions from the cover-piece fundamental groupoids to the
ambient fundamental groupoid. -/
def pieceFundamentalGroupoidMap (b : Bool) :
    FundamentalGroupoid (CoverPiece U V b) ⥤ FundamentalGroupoid X :=
  FundamentalGroupoid.map (coverPieceInclusion b)

/-- Both span composites are the same functor to the ambient fundamental
groupoid.  The equality is propositional because functoriality of
`FundamentalGroupoid.map` is stated propositionally. -/
theorem overlap_ambient_functor_eq :
    overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙
        pieceFundamentalGroupoidMap (U := U) (V := V) true =
      overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙
        pieceFundamentalGroupoidMap (U := U) (V := V) false := by
  unfold overlapFundamentalGroupoidMap pieceFundamentalGroupoidMap
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  rw [overlap_piece_ambient_comp true, overlap_piece_ambient_comp false]

/-- The actual ambient cocone over the fundamental-groupoid span. -/
structure AmbientSpanCocone where
  left : FundamentalGroupoid (CoverPiece U V true) ⥤ FundamentalGroupoid X
  right : FundamentalGroupoid (CoverPiece U V false) ⥤ FundamentalGroupoid X
  condition : overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙ left =
    overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙ right

def ambientSpanCocone : AmbientSpanCocone (X := X) (U := U) (V := V) where
  left := pieceFundamentalGroupoidMap true
  right := pieceFundamentalGroupoidMap false
  condition := overlap_ambient_functor_eq

/-- Strict functor-valued cocones demand literal equality after restriction. -/
structure StrictFunctorCocone where
  left : FundamentalGroupoid (CoverPiece U V true) ⥤ C
  right : FundamentalGroupoid (CoverPiece U V false) ⥤ C
  condition : overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙ left =
    overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙ right

/-- The honest 2-categorical cocone interface: overlap restrictions are
identified by a specified natural isomorphism, not required to be equal. -/
structure PseudoFunctorCocone where
  left : FundamentalGroupoid (CoverPiece U V true) ⥤ C
  right : FundamentalGroupoid (CoverPiece U V false) ⥤ C
  glue : overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙ left ≅
    overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙ right

/-- The overlap component dictated by a `TwoOpenDescentDatum`'s common object
coordinates. -/
def descentOverlapAppIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (z : FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V))) :
    ((overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙ D.functor true).obj z) ≅
      ((overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙ D.functor false).obj z) :=
  eqToIso ((D.obj_eq true
    ((overlapFundamentalGroupoidMap (U := U) (V := V) true).obj z)).trans
      ((congrArg D.obj (show
        ((overlapFundamentalGroupoidMap (U := U) (V := V) true).obj z).as.1 =
          ((overlapFundamentalGroupoidMap (U := U) (V := V) false).obj z).as.1
        from rfl)).trans
        (D.obj_eq false
          ((overlapFundamentalGroupoidMap (U := U) (V := V) false).obj z)).symm))

/-- Object-level pseudococone data extracted from descent data.  Naturality of
`descentOverlapAppIso` is precisely the `overlap_eq` field after translating
paths in the nested overlap subtype. -/
def descentPseudoCoconeObject
    (D : @TwoOpenDescentDatum X _ U V C _) :
    (FundamentalGroupoid (CoverPiece U V true) ⥤ C) ×
      (FundamentalGroupoid (CoverPiece U V false) ⥤ C) :=
  (D.functor true, D.functor false)

#print axioms overlap_piece_ambient_comp
#print axioms overlap_ambient_functor_eq
#print axioms ambientSpanCocone
#print axioms descentOverlapAppIso

end ConstructionTargets.TwoOpenFundamentalGroupoidSpan
