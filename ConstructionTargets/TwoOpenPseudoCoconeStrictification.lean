import ConstructionTargets.TwoOpenFundamentalGroupoidSpan

/-!
# Strictification data for two-open pseudococones

An arbitrary pseudococone identifies overlap objects by isomorphisms, whereas
`TwoOpenDescentDatum.obj_eq` requires equality with a chosen common object.
This file states the exact extra coordinate data needed for the reverse
construction and implements that construction.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenPseudoCoconeStrictification

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.TwoOpenDescentCategory
open ConstructionTargets.TwoOpenFundamentalGroupoidSpan

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- Naturality through an isomorphism, solved without changing any endpoint
objects: conjugating the target arrow gives the source arrow. -/
theorem iso_naturality_conjugation
    {L₀ L₁ R₀ R₁ : C} (l : L₀ ⟶ L₁) (r : R₀ ⟶ R₁)
    (e₀ : L₀ ≅ R₀) (e₁ : L₁ ≅ R₁)
    (h : l ≫ e₁.hom = e₀.hom ≫ r) :
    e₀.hom ≫ r ≫ e₁.inv = l := by
  rw [← Category.assoc, ← h]
  simp [Category.assoc]

/-- Mapping the canonical overlap lift of an ambient path to either piece
gives the corresponding `pathInPiece` arrow.  Endpoint membership witnesses
are aligned only after the path has been constructed. -/
theorem overlapPath_map_eq_pathInPiece
    {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V) (b : Bool) :
    let xW : CoverOverlap (X := X) (U := U) (V := V) :=
      ⟨x, by simpa using hU 0, by simpa using hV 0⟩
    let yW : CoverOverlap (X := X) (U := U) (V := V) :=
      ⟨y, by simpa using hU 1, by simpa using hV 1⟩
    let pW : Path xW yW :=
      { toFun := fun t ↦ ⟨p t, hU t, hV t⟩
        continuous_toFun := p.continuous.subtype_mk _
        source' := Subtype.ext p.source
        target' := Subtype.ext p.target }
    let hp : ∀ t, p t ∈ twoChart U V b := by
      cases b
      · simpa [twoChart] using hV
      · simpa [twoChart] using hU
    let xb : FundamentalGroupoid (CoverPiece U V b) :=
      ⟨⟨x, by simpa using hp 0⟩⟩
    let yb : FundamentalGroupoid (CoverPiece U V b) :=
      ⟨⟨y, by simpa using hp 1⟩⟩
    let hx : xb.as = ((overlapFundamentalGroupoidMap
        (U := U) (V := V) b).obj ⟨xW⟩).as :=
      by
        cases b
        apply Subtype.ext
        rfl
        apply Subtype.ext
        rfl
    let hy : yb.as = ((overlapFundamentalGroupoidMap
        (U := U) (V := V) b).obj ⟨yW⟩).as :=
      by
        cases b
        apply Subtype.ext
        rfl
        apply Subtype.ext
        rfl
    let ex := congrArg FundamentalGroupoid.mk hx
    let ey := congrArg FundamentalGroupoid.mk hy
    eqToHom ex ≫
        (overlapFundamentalGroupoidMap (U := U) (V := V) b).map
          (Path.Homotopic.Quotient.mk pW) ≫
        eqToHom ey.symm =
      Path.Homotopic.Quotient.mk (pathInPiece U V b p hp) := by
  dsimp only
  change eqToHom _ ≫
      FundamentalGroupoid.fromPath
        ((Path.Homotopic.Quotient.mk _).map
          (overlapToPiece (U := U) (V := V) b)) ≫
      eqToHom _ = _
  rw [← Path.Homotopic.Quotient.mk_map]
  rw [FundamentalGroupoid.conj_eqToHom]
  all_goals cases b <;>
    simp [pathInPiece, overlapToPiece]
  all_goals
    congr 1

/-- A pseudococone together with a strict common object coordinate.  The last
field is the overlap map equation in those coordinates; it is the exact form
required by `TwoOpenDescentDatum.overlap_eq`. -/
structure CoordinatedPseudoFunctorCocone where
  pseudo : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)
  obj : X → C
  left_obj_eq : ∀ z : FundamentalGroupoid (CoverPiece U V true),
    pseudo.left.obj z = obj z.as.1
  right_obj_eq : ∀ z : FundamentalGroupoid (CoverPiece U V false),
    pseudo.right.obj z = obj z.as.1
  glue_app_eq : ∀ z : FundamentalGroupoid
      (CoverOverlap (X := X) (U := U) (V := V)),
    pseudo.glue.app z = eqToIso ((left_obj_eq
      ((overlapFundamentalGroupoidMap (U := U) (V := V) true).obj z)).trans
        ((congrArg obj (show
          ((overlapFundamentalGroupoidMap (U := U) (V := V) true).obj z).as.1 =
            ((overlapFundamentalGroupoidMap (U := U) (V := V) false).obj z).as.1
          from rfl)).trans
          (right_obj_eq
            ((overlapFundamentalGroupoidMap (U := U) (V := V) false).obj z)).symm))
  overlap_eq : ∀ {x y : X} (p : Path x y)
      (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V),
    eqToHom (right_obj_eq ⟨⟨x, by simpa [twoChart] using hV 0⟩⟩).symm ≫
        pseudo.right.map (Path.Homotopic.Quotient.mk
          (pathInPiece U V false p (by simpa [twoChart] using hV))) ≫
        eqToHom (right_obj_eq ⟨⟨y, by simpa [twoChart] using hV 1⟩⟩) =
      eqToHom (left_obj_eq ⟨⟨x, by simpa [twoChart] using hU 0⟩⟩).symm ≫
        pseudo.left.map (Path.Homotopic.Quotient.mk
          (pathInPiece U V true p (by simpa [twoChart] using hU))) ≫
        eqToHom (left_obj_eq ⟨⟨y, by simpa [twoChart] using hU 1⟩⟩)

/-- The two piece functors, selected with a dependent Boolean match. -/
def CoordinatedPseudoFunctorCocone.pieceFunctor
    (P : CoordinatedPseudoFunctorCocone
      (U := U) (V := V) (C := C)) :
    (b : Bool) → FundamentalGroupoid (CoverPiece U V b) ⥤ C
  | false => P.pseudo.right
  | true => P.pseudo.left

/-- Reverse construction once a pseudococone has been strictified to common
object coordinates. -/
def CoordinatedPseudoFunctorCocone.toDescentObject
    (P : CoordinatedPseudoFunctorCocone
      (U := U) (V := V) (C := C)) :
    DescentObject (X := X) (U := U) (V := V) (C := C) :=
  ⟨{
    obj := P.obj
    functor := P.pieceFunctor
    obj_eq := by
      intro b z
      cases b
      · exact P.right_obj_eq z
      · exact P.left_obj_eq z
    overlap_eq := by
      intro x y p hU hV
      simpa using P.overlap_eq p hU hV
  }⟩

@[simp] theorem toDescentObject_obj
    (P : CoordinatedPseudoFunctorCocone
      (U := U) (V := V) (C := C)) (x : X) :
    P.toDescentObject.datum.obj x = P.obj x := rfl

@[simp] theorem toDescentObject_functor_true
    (P : CoordinatedPseudoFunctorCocone
      (U := U) (V := V) (C := C)) :
    P.toDescentObject.datum.functor true = P.pseudo.left := rfl

@[simp] theorem toDescentObject_functor_false
    (P : CoordinatedPseudoFunctorCocone
      (U := U) (V := V) (C := C)) :
    P.toDescentObject.datum.functor false = P.pseudo.right := rfl

/-- The exact object-equality data missing from an arbitrary pseudococone.
This proposition is intentionally exposed rather than manufactured from
`P.glue`, which only gives isomorphisms. -/
def HasStrictCommonObjectCoordinates
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) : Prop :=
  ∃ (obj : X → C),
    (∀ z : FundamentalGroupoid (CoverPiece U V true),
      P.left.obj z = obj z.as.1) ∧
    (∀ z : FundamentalGroupoid (CoverPiece U V false),
      P.right.obj z = obj z.as.1)

#print axioms CoordinatedPseudoFunctorCocone
#print axioms CoordinatedPseudoFunctorCocone.toDescentObject
#print axioms HasStrictCommonObjectCoordinates

end ConstructionTargets.TwoOpenPseudoCoconeStrictification
