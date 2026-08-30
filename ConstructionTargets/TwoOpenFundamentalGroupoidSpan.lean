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

theorem overlap_naturality_of_conjugated
    {T₀ T₁ F₀ F₁ O₀ O₁ : C} (t : T₀ ⟶ T₁) (f : F₀ ⟶ F₁)
    (dt₀ : T₀ = O₀) (dt₁ : T₁ = O₁) (df₀ : F₀ = O₀) (df₁ : F₁ = O₁)
    (h : eqToHom df₀.symm ≫ f ≫ eqToHom df₁ =
      eqToHom dt₀.symm ≫ t ≫ eqToHom dt₁) :
    t ≫ eqToHom (dt₁.trans df₁.symm) =
      eqToHom (dt₀.trans df₀.symm) ≫ f := by
  subst O₀
  subst O₁
  subst F₀
  subst F₁
  simp_all

/-- Naturality of the overlap comparison.  The representative is a path in
the nested overlap subtype; forgetting both subtype layers gives the ambient
path to which `TwoOpenDescentDatum.overlap_eq` applies. -/
theorem descentOverlapAppIso_naturality
    (D : @TwoOpenDescentDatum X _ U V C _)
    {x y : FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V))}
    (f : x ⟶ y) :
    (overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙
        D.functor true).map f ≫ (descentOverlapAppIso D y).hom =
      (descentOverlapAppIso D x).hom ≫
        (overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙
          D.functor false).map f := by
  induction f using Quotient.inductionOn with
  | _ p =>
    let q : Path x.as.1 y.as.1 := p.map continuous_subtype_val
    have hU : ∀ t, q t ∈ U := fun t => (p t).2.1
    have hV : ∀ t, q t ∈ V := fun t => (p t).2.2
    apply overlap_naturality_of_conjugated _ _
      (D.obj_eq true ((overlapFundamentalGroupoidMap
        (U := U) (V := V) true).obj x))
      (D.obj_eq true ((overlapFundamentalGroupoidMap
        (U := U) (V := V) true).obj y))
      (D.obj_eq false ((overlapFundamentalGroupoidMap
        (U := U) (V := V) false).obj x))
      (D.obj_eq false ((overlapFundamentalGroupoidMap
        (U := U) (V := V) false).obj y))
    simpa [overlapFundamentalGroupoidMap, FundamentalGroupoid.map, q,
      pathInPiece, overlapToPiece, ← Path.Homotopic.Quotient.mk_map,
      Category.assoc] using D.overlap_eq q hU hV

/-- The natural overlap isomorphism carried by descent data. -/
def descentOverlapIso (D : @TwoOpenDescentDatum X _ U V C _) :
    overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙ D.functor true ≅
      overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙ D.functor false :=
  NatIso.ofComponents (descentOverlapAppIso D)
    (descentOverlapAppIso_naturality D)

/-- Object-level pseudococone data extracted from descent data.  Naturality of
`descentOverlapAppIso` is precisely the `overlap_eq` field after translating
paths in the nested overlap subtype. -/
def descentPseudoCoconeObject
    (D : @TwoOpenDescentDatum X _ U V C _) :
    (FundamentalGroupoid (CoverPiece U V true) ⥤ C) ×
      (FundamentalGroupoid (CoverPiece U V false) ⥤ C) :=
  (D.functor true, D.functor false)

/-- Descent data determines an honest pseudococone over the two-open span. -/
def descentPseudoCocone
    (D : @TwoOpenDescentDatum X _ U V C _) :
    PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C) where
  left := D.functor true
  right := D.functor false
  glue := descentOverlapIso D

/-- A morphism of pseudococones is a pair of transformations compatible with
the specified overlap 2-cells. -/
structure PseudoFunctorCoconeHom
    (P Q : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) where
  left : P.left ⟶ Q.left
  right : P.right ⟶ Q.right
  glue_naturality : P.glue.hom ≫
      Functor.whiskerLeft (overlapFundamentalGroupoidMap
        (U := U) (V := V) false) right =
    Functor.whiskerLeft (overlapFundamentalGroupoidMap
        (U := U) (V := V) true) left ≫ Q.glue.hom

@[ext] theorem PseudoFunctorCoconeHom.ext
    {P Q : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)}
    {α β : PseudoFunctorCoconeHom P Q}
    (hl : α.left = β.left) (hr : α.right = β.right) : α = β := by
  cases α
  cases β
  simp_all

instance : Category (PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) where
  Hom := PseudoFunctorCoconeHom
  id P := { left := 𝟙 P.left, right := 𝟙 P.right, glue_naturality := by simp }
  comp α β := {
    left := α.left ≫ β.left
    right := α.right ≫ β.right
    glue_naturality := by
      rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
      rw [← Category.assoc, α.glue_naturality]
      simp only [Category.assoc]
      rw [β.glue_naturality]
      }
  id_comp _ := by ext <;> simp
  comp_id _ := by ext <;> simp
  assoc _ _ _ := by ext <;> simp [Category.assoc]

/-- Postcompose both legs and the overlap isomorphism of a pseudococone. -/
def postcomposePseudoFunctorCoconeObj {D : Type*} [Category D] (H : C ⥤ D)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :
    PseudoFunctorCocone (X := X) (U := U) (V := V) (C := D) where
  left := P.left ⋙ H
  right := P.right ⋙ H
  glue := Functor.isoWhiskerRight P.glue H

/-- Postcompose a pseudococone morphism componentwise. -/
def postcomposePseudoFunctorCoconeMap {D : Type*} [Category D] (H : C ⥤ D)
    {P Q : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)}
    (tau : P ⟶ Q) :
    postcomposePseudoFunctorCoconeObj H P ⟶
      postcomposePseudoFunctorCoconeObj H Q where
  left := Functor.whiskerRight tau.left H
  right := Functor.whiskerRight tau.right H
  glue_naturality := by
    ext z
    simpa [postcomposePseudoFunctorCoconeObj] using
      congrArg H.map (NatTrans.congr_app tau.glue_naturality z)

/-- Postcomposition is functorial on the category of pseudococones. -/
def postcomposePseudoFunctorCoconeFunctor {D : Type*} [Category D] (H : C ⥤ D) :
    PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C) ⥤
      PseudoFunctorCocone (X := X) (U := U) (V := V) (C := D) where
  obj := postcomposePseudoFunctorCoconeObj H
  map := postcomposePseudoFunctorCoconeMap H
  map_id P := by
    apply PseudoFunctorCoconeHom.ext <;> ext z
    · change H.map (𝟙 _) = 𝟙 _
      simp
    · change H.map (𝟙 _) = 𝟙 _
      simp
  map_comp f g := by
    apply PseudoFunctorCoconeHom.ext <;> ext z
    · change H.map (f.left.app z ≫ g.left.app z) =
        H.map (f.left.app z) ≫ H.map (g.left.app z)
      simp
    · change H.map (f.right.app z ≫ g.right.app z) =
        H.map (f.right.app z) ≫ H.map (g.right.app z)
      simp

@[simp] theorem postcomposePseudoFunctorCoconeObj_left
    {D : Type*} [Category D] (H : C ⥤ D)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :
    (postcomposePseudoFunctorCoconeObj H P).left = P.left ⋙ H := rfl

@[simp] theorem postcomposePseudoFunctorCoconeObj_right
    {D : Type*} [Category D] (H : C ⥤ D)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :
    (postcomposePseudoFunctorCoconeObj H P).right = P.right ⋙ H := rfl

@[simp] theorem postcomposePseudoFunctorCoconeMap_left
    {D : Type*} [Category D] (H : C ⥤ D)
    {P Q : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)}
    (tau : P ⟶ Q) :
    (postcomposePseudoFunctorCoconeMap H tau).left =
      Functor.whiskerRight tau.left H := rfl

@[simp] theorem postcomposePseudoFunctorCoconeMap_right
    {D : Type*} [Category D] (H : C ⥤ D)
    {P Q : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)}
    (tau : P ⟶ Q) :
    (postcomposePseudoFunctorCoconeMap H tau).right =
      Functor.whiskerRight tau.right H := rfl

theorem glue_square_of_common_coordinate
    {DT DF ET EF O P : C} (aT : DT ⟶ ET) (aF : DF ⟶ EF)
    (dt : DT = O) (df : DF = O) (et : ET = P) (ef : EF = P)
    (h : eqToHom df.symm ≫ aF ≫ eqToHom ef =
      eqToHom dt.symm ≫ aT ≫ eqToHom et) :
    eqToHom (dt.trans df.symm) ≫ aF =
      aT ≫ eqToHom (et.trans ef.symm) := by
  subst O
  subst P
  subst DF
  subst EF
  simp_all

/-- Compatible transformations give precisely the morphisms between the
associated pseudococones. -/
def descentPseudoCoconeMap
    {D E : @TwoOpenDescentDatum X _ U V C _}
    (τ : ConstructionTargets.TwoOpenDescentFullness.CompatibleNatTrans D E) :
    descentPseudoCocone D ⟶ descentPseudoCocone E where
  left := τ.piece true
  right := τ.piece false
  glue_naturality := by
    ext z
    change (descentOverlapAppIso D z).hom ≫ (τ.piece false).app _ =
      (τ.piece true).app _ ≫ (descentOverlapAppIso E z).hom
    apply glue_square_of_common_coordinate
      ((τ.piece true).app _ ) ((τ.piece false).app _)
      (D.obj_eq true _) (D.obj_eq false _)
      (E.obj_eq true _) (E.obj_eq false _)
    exact τ.overlap_app z.as.1 z.as.2.1 z.as.2.2

/-- Forgetting the chosen common object coordinates sends descent objects and
compatible transformations to pseudococones and their commuting 2-cells. -/
def descentToPseudoCoconeFunctor :
    ConstructionTargets.TwoOpenDescentCategory.DescentObject
        (X := X) (U := U) (V := V) (C := C) ⥤
      PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C) where
  obj D := descentPseudoCocone D.datum
  map τ := descentPseudoCoconeMap τ
  map_id D := by
    apply PseudoFunctorCoconeHom.ext <;> rfl
  map_comp τ σ := by
    apply PseudoFunctorCoconeHom.ext <;> rfl

/-- A common object coordinate chosen from the left piece whenever possible,
and otherwise from the right piece. -/
def strictifiedObject (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (x : X) : C := by
  classical
  exact if hx : x ∈ U then P.left.obj ⟨⟨x, hx⟩⟩ else
    P.right.obj ⟨⟨x, by
      have : x ∈ U ∪ V := by rw [hcover]; trivial
      exact this.resolve_left hx⟩⟩

def pseudoPieceFunctor
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C)) :
    (b : Bool) → FundamentalGroupoid (CoverPiece U V b) ⥤ C
  | false => P.right
  | true => P.left

/-- The original piece object is isomorphic to its chosen common coordinate.
On the right piece inside the overlap this is the inverse glue component. -/
def strictifiedObjectIso (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (b : Bool) (z : FundamentalGroupoid (CoverPiece U V b)) :
    (pseudoPieceFunctor P b).obj z ≅ strictifiedObject hcover P z.as.1 := by
  classical
  cases b
  · by_cases hx : z.as.1 ∈ U
    · let w : FundamentalGroupoid (CoverOverlap (X := X) (U := U) (V := V)) :=
        ⟨⟨z.as.1, hx, by simpa [twoChart] using z.as.2⟩⟩
      let zr := (overlapFundamentalGroupoidMap
        (U := U) (V := V) false).obj w
      let zl := (overlapFundamentalGroupoidMap
        (U := U) (V := V) true).obj w
      have hr : zr = z := by
        apply FundamentalGroupoid.ext
        rfl
      let zl' : FundamentalGroupoid (CoverPiece U V true) :=
        ⟨⟨z.as.1, hx⟩⟩
      have hzl : zl = zl' := by
        apply FundamentalGroupoid.ext
        rfl
      have hl : P.left.obj zl = strictifiedObject hcover P z.as.1 := by
        rw [congrArg P.left.obj hzl]
        simp [strictifiedObject, hx, zl']
      exact eqToIso (congrArg P.right.obj hr.symm) ≪≫
        (P.glue.app w).symm ≪≫ eqToIso hl
    · exact eqToIso (by
        change P.right.obj z = _
        simp [strictifiedObject, hx])
  · exact eqToIso (by
      change P.left.obj z = _
      simp [strictifiedObject, z.as.2])

/-- Conjugating a piece functor through `strictifiedObjectIso` replaces its
object map by the literal common object function. -/
def strictifiedPieceFunctor (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (b : Bool) : FundamentalGroupoid (CoverPiece U V b) ⥤ C where
  obj z := strictifiedObject hcover P z.as.1
  map {x y} f := (strictifiedObjectIso hcover P b x).inv ≫
    (pseudoPieceFunctor P b).map f ≫
    (strictifiedObjectIso hcover P b y).hom
  map_id x := by simp
  map_comp f g := by simp [Category.assoc]

/-- Comparison from each original piece functor to its strictified copy. -/
def pieceStrictificationIso (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (b : Bool) :
    pseudoPieceFunctor P b ≅ strictifiedPieceFunctor hcover P b :=
  NatIso.ofComponents (strictifiedObjectIso hcover P b) (by
    intro x y f
    simp [strictifiedPieceFunctor, Category.assoc])

theorem strictifiedPieceFunctor_obj_eq (hcover : U ∪ V = Set.univ)
    (P : PseudoFunctorCocone (X := X) (U := U) (V := V) (C := C))
    (b : Bool) (z : FundamentalGroupoid (CoverPiece U V b)) :
    (strictifiedPieceFunctor hcover P b).obj z =
      strictifiedObject hcover P z.as.1 := rfl

#print axioms overlap_piece_ambient_comp
#print axioms overlap_ambient_functor_eq
#print axioms ambientSpanCocone
#print axioms descentOverlapAppIso
#print axioms descentOverlapAppIso_naturality
#print axioms descentOverlapIso
#print axioms descentPseudoCocone
#print axioms postcomposePseudoFunctorCoconeFunctor
#print axioms descentPseudoCoconeMap
#print axioms descentToPseudoCoconeFunctor
#print axioms strictifiedPieceFunctor
#print axioms pieceStrictificationIso

end ConstructionTargets.TwoOpenFundamentalGroupoidSpan
