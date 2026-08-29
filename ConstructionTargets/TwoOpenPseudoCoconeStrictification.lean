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

theorem functor_map_eqToHom {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {x y : A} (h : x = y) :
    F.map (eqToHom h) = eqToHom (congrArg F.obj h) := by
  subst y
  simp

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

/-- On an overlap point, the right strictification comparison is the inverse
glue comparison followed by the left strictification comparison, with the
independently constructed subtype objects transported explicitly. -/
theorem strictifiedObjectIso_overlap_hom
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (x : X) (hU : x ∈ U) (hV : x ∈ V) :
    let xW : FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V)) :=
      ⟨⟨x, hU, hV⟩⟩
    let xL : FundamentalGroupoid (CoverPiece U V true) :=
      ⟨⟨x, by simpa [twoChart] using hU⟩⟩
    let xR : FundamentalGroupoid (CoverPiece U V false) :=
      ⟨⟨x, by simpa [twoChart] using hV⟩⟩
    let eL : xL = (overlapFundamentalGroupoidMap
        (U := U) (V := V) true).obj xW := by
      apply FundamentalGroupoid.ext; rfl
    let eR : xR = (overlapFundamentalGroupoidMap
        (U := U) (V := V) false).obj xW := by
      apply FundamentalGroupoid.ext; rfl
    (strictifiedObjectIso hcover P false xR).hom =
      eqToHom (congrArg P.right.obj eR) ≫ (P.glue.app xW).inv ≫
        eqToHom (congrArg P.left.obj eL).symm ≫
          (strictifiedObjectIso hcover P true xL).hom := by
  dsimp only
  simp [strictifiedObjectIso, strictifiedObject, hU]
  congr 1
  congr 1
  exact (eqToHom_trans _ _).symm

/-- Iso-valued form of `strictifiedObjectIso_overlap_hom`, used to normalize
both the source inverse and target hom in a conjugated map. -/
theorem strictifiedObjectIso_overlap
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (x : X) (hU : x ∈ U) (hV : x ∈ V) :
    let xW : FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V)) :=
      ⟨⟨x, hU, hV⟩⟩
    let xL : FundamentalGroupoid (CoverPiece U V true) :=
      ⟨⟨x, by simpa [twoChart] using hU⟩⟩
    let xR : FundamentalGroupoid (CoverPiece U V false) :=
      ⟨⟨x, by simpa [twoChart] using hV⟩⟩
    let eL : xL = (overlapFundamentalGroupoidMap
        (U := U) (V := V) true).obj xW := by
      apply FundamentalGroupoid.ext; rfl
    let eR : xR = (overlapFundamentalGroupoidMap
        (U := U) (V := V) false).obj xW := by
      apply FundamentalGroupoid.ext; rfl
    strictifiedObjectIso hcover P false xR =
      eqToIso (congrArg P.right.obj eR) ≪≫ (P.glue.app xW).symm ≪≫
        eqToIso (congrArg P.left.obj eL).symm ≪≫
          strictifiedObjectIso hcover P true xL := by
  apply Iso.ext
  exact strictifiedObjectIso_overlap_hom hcover P x hU hV

/-- The overlap comparison after replacing both piece functors by their
common-object strictifications. -/
def strictifiedOverlapIso
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :
    overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙
        strictifiedPieceFunctor hcover P true ≅
      overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙
        strictifiedPieceFunctor hcover P false :=
  Functor.isoWhiskerLeft
      (overlapFundamentalGroupoidMap (U := U) (V := V) true)
      (pieceStrictificationIso hcover P true).symm ≪≫
    P.glue ≪≫
    Functor.isoWhiskerLeft
      (overlapFundamentalGroupoidMap (U := U) (V := V) false)
      (pieceStrictificationIso hcover P false)

/-- Cancellation entirely within one target category.  The four objects allow
the canonical overlap images and independently built piece lifts to remain
distinct until their explicit equality transports have been composed. -/
theorem transported_glue_strictification_identity
    {L R L' R' O : C} (eL : L' = L) (eR : R' = R)
    (g : L ≅ R) (sL : L' ≅ O) (sR : R' ≅ O)
    (hsR : sR = eqToIso eR ≪≫ g.symm ≪≫ eqToIso eL.symm ≪≫ sL) :
    sL.inv ≫ eqToHom eL ≫ g.hom ≫ eqToHom eR.symm ≫ sR.hom =
      𝟙 O := by
  rw [hsR]
  subst L
  subst R
  simp

@[simp] theorem strictifiedOverlapIso_hom_app
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (z : FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V))) :
    (strictifiedOverlapIso hcover P).hom.app z = 𝟙 _ := by
  rcases z with ⟨⟨x, hU, hV⟩⟩
  let xW : FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V)) :=
    ⟨⟨x, hU, hV⟩⟩
  let xL : FundamentalGroupoid (CoverPiece U V true) :=
    ⟨⟨x, by simpa [twoChart] using hU⟩⟩
  let xR : FundamentalGroupoid (CoverPiece U V false) :=
    ⟨⟨x, by simpa [twoChart] using hV⟩⟩
  let eL : xL = (overlapFundamentalGroupoidMap
      (U := U) (V := V) true).obj xW := by
    apply FundamentalGroupoid.ext; rfl
  let eR : xR = (overlapFundamentalGroupoidMap
      (U := U) (V := V) false).obj xW := by
    apply FundamentalGroupoid.ext; rfl
  have hs := strictifiedObjectIso_overlap hcover P x hU hV
  have ht := transported_glue_strictification_identity
    (congrArg P.left.obj eL) (congrArg P.right.obj eR)
    (P.glue.app xW) (strictifiedObjectIso hcover P true xL)
    (strictifiedObjectIso hcover P false xR) hs
  change (strictifiedObjectIso hcover P true _).inv ≫
      (P.glue.app _).hom ≫
      (strictifiedObjectIso hcover P false _).hom = 𝟙 _
  convert ht using 1 <;>
    simp [xW, xL, xR, eL, eR, overlapFundamentalGroupoidMap,
      overlapToPiece, FundamentalGroupoid.map]
  apply eq_of_heq
  rfl

/-- Naturality of an overlap comparison with identity components says that
the two strictified overlap functors have the same map. -/
theorem strictifiedOverlapIso_map_eq
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    {x y : FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V))}
    (f : x ⟶ y) :
    (overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙
      strictifiedPieceFunctor hcover P true).map f =
    (overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙
      strictifiedPieceFunctor hcover P false).map f := by
  have h := (strictifiedOverlapIso hcover P).hom.naturality f
  rw [strictifiedOverlapIso_hom_app, strictifiedOverlapIso_hom_app] at h
  calc
    _ = _ ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = 𝟙 _ ≫ _ := h
    _ = _ := Category.id_comp _

/-- The strictified piece maps agree on every ambient overlap path, in the
exact independently constructed `pathInPiece` presentations. -/
theorem strictified_overlap_map_eq
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V) :
    (strictifiedPieceFunctor hcover P false).map
        (Path.Homotopic.Quotient.mk
          (pathInPiece U V false p (by simpa [twoChart] using hV))) =
      (strictifiedPieceFunctor hcover P true).map
        (Path.Homotopic.Quotient.mk
          (pathInPiece U V true p (by simpa [twoChart] using hU))) := by
  let xW : CoverOverlap (X := X) (U := U) (V := V) :=
    ⟨x, by simpa using hU 0, by simpa using hV 0⟩
  let yW : CoverOverlap (X := X) (U := U) (V := V) :=
    ⟨y, by simpa using hU 1, by simpa using hV 1⟩
  let pW : Path xW yW :=
    { toFun := fun t => ⟨p t, hU t, hV t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  have hn := strictifiedOverlapIso_map_eq hcover P
    (Path.Homotopic.Quotient.mk pW)
  have hL := overlapPath_map_eq_pathInPiece p hU hV true
  have hR := overlapPath_map_eq_pathInPiece p hU hV false
  dsimp only at hL hR
  have hmL := congrArg (fun f =>
    (strictifiedPieceFunctor hcover P true).map f) hL
  have hmR := congrArg (fun f =>
    (strictifiedPieceFunctor hcover P false).map f) hR
  simp only [Functor.map_comp, functor_map_eqToHom] at hmL hmR
  change eqToHom (_ : strictifiedObject hcover P x =
      strictifiedObject hcover P x) ≫ _ ≫
      eqToHom (_ : strictifiedObject hcover P y =
        strictifiedObject hcover P y) = _ at hmL
  change eqToHom (_ : strictifiedObject hcover P x =
      strictifiedObject hcover P x) ≫ _ ≫
      eqToHom (_ : strictifiedObject hcover P y =
        strictifiedObject hcover P y) = _ at hmR
  have hmL' :
      (strictifiedPieceFunctor hcover P true).map
          ((overlapFundamentalGroupoidMap (U := U) (V := V) true).map
            (Path.Homotopic.Quotient.mk pW)) =
        (strictifiedPieceFunctor hcover P true).map
          (Path.Homotopic.Quotient.mk
            (pathInPiece U V true p (by simpa [twoChart] using hU))) := by
    simpa [strictifiedPieceFunctor, strictifiedObject] using hmL
  have hmR' :
      (strictifiedPieceFunctor hcover P false).map
          ((overlapFundamentalGroupoidMap (U := U) (V := V) false).map
            (Path.Homotopic.Quotient.mk pW)) =
        (strictifiedPieceFunctor hcover P false).map
          (Path.Homotopic.Quotient.mk
            (pathInPiece U V false p (by simpa [twoChart] using hV))) := by
    simpa [strictifiedPieceFunctor, strictifiedObject] using hmR
  rw [← hmR', ← hmL']
  exact hn.symm

/-- Every pseudococone admits descent data after conjugating its piece
functors into the chosen common object coordinates. -/
def strictifiedDescentDatum
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :
    @TwoOpenDescentDatum X _ U V C _ where
  obj := strictifiedObject hcover P
  functor := strictifiedPieceFunctor hcover P
  obj_eq := strictifiedPieceFunctor_obj_eq hcover P
  overlap_eq := by
    intro x y p hU hV
    simpa [strictifiedPieceFunctor_obj_eq] using
      strictified_overlap_map_eq hcover P p hU hV

/-- Object of the repository descent category obtained by strictification. -/
def strictifiedDescentObject
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :
    DescentObject (X := X) (U := U) (V := V) (C := C) :=
  ⟨strictifiedDescentDatum hcover P⟩

/-- The original pieces compare naturally to the two functors of the
strictified descent object. -/
def strictifiedDescentPieceIso
    (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (b : Bool) :
    pseudoPieceFunctor P b ≅ (strictifiedDescentDatum hcover P).functor b :=
  pieceStrictificationIso hcover P b

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
#print axioms transported_glue_strictification_identity
#print axioms strictifiedOverlapIso
#print axioms strictifiedOverlapIso_hom_app
#print axioms strictifiedOverlapIso_map_eq
#print axioms strictified_overlap_map_eq
#print axioms strictifiedDescentDatum
#print axioms strictifiedDescentObject
#print axioms strictifiedDescentPieceIso

end ConstructionTargets.TwoOpenPseudoCoconeStrictification
