import ConstructionTargets.TwoOpenDescentUniqueness
import ConstructionTargets.HomotopySquareStripDescent

/-!
# Existence data for two-open descent 2-cells

This file packages compatible natural transformations on the two cover
pieces and constructs their well-defined common-coordinate component on every
ambient object.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenDescentFullness

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.TwoOpenDescentRestriction
open ConstructionTargets.TwoOpenDescentFunctor
open ConstructionTargets.TwoOpenDescentQuotient
open ConstructionTargets.HomotopySquareStripDescent

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- Naturality is preserved when both functors' source and target objects are
transported to common coordinates.  Stating the four equalities explicitly
keeps proof-irrelevant `eqToHom` witnesses from becoming a downstream
syntactic requirement. -/
theorem transported_naturality
    {P₀ P₁ Q₀ Q₁ D₀ D₁ E₀ E₁ : C}
    (f : P₀ ⟶ P₁) (g : Q₀ ⟶ Q₁)
    (a₀ : P₀ ⟶ Q₀) (a₁ : P₁ ⟶ Q₁)
    (h : f ≫ a₁ = a₀ ≫ g)
    (d₀ : P₀ = D₀) (d₁ : P₁ = D₁)
    (e₀ : Q₀ = E₀) (e₁ : Q₁ = E₁) :
    (eqToHom d₀.symm ≫ f ≫ eqToHom d₁) ≫
        (eqToHom d₁.symm ≫ a₁ ≫ eqToHom e₁) =
      (eqToHom d₀.symm ≫ a₀ ≫ eqToHom e₀) ≫
        (eqToHom e₀.symm ≫ g ≫ eqToHom e₁) := by
  subst D₀
  subst D₁
  subst E₀
  subst E₁
  simpa using h

/-- Transporting a dependent morphism family along the same index equality at
both endpoints recovers its component at the transported index. -/
theorem dependent_component_transport {I : Type*} (A B : I → C)
    (a : (i : I) → A i ⟶ B i) {i j : I} (h : i = j) :
    eqToHom (congrArg A h).symm ≫ a i ≫ eqToHom (congrArg B h) = a j := by
  subst j
  simp

theorem dependent_component_transport_forward {I : Type*} (A B : I → C)
    (a : (i : I) → A i ⟶ B i) {i j : I} (h : i = j) :
    eqToHom (congrArg A h) ≫ a j = a i ≫ eqToHom (congrArg B h) := by
  subst j
  simp

theorem dependent_component_transport_backward {I : Type*} (A B : I → C)
    (a : (i : I) → A i ⟶ B i) {i j : I} (h : i = j) :
    a j ≫ eqToHom (congrArg B h).symm =
      eqToHom (congrArg A h).symm ≫ a i := by
  subst j
  simp

/-- Recovering a morphism from its common-coordinate conjugate. -/
theorem conjugation_recover {P Q D₀ E₀ : C} (a : P ⟶ Q)
    (d : P = D₀) (e : Q = E₀) :
    a ≫ eqToHom e =
      eqToHom d ≫ (eqToHom d.symm ≫ a ≫ eqToHom e) := by
  subst D₀
  subst E₀
  simp

theorem whisker_two_of_eq {A B D₀ E₀ : C} {a b : A ⟶ B}
    (h : a = b) (f : B ⟶ D₀) (g : D₀ ⟶ E₀) :
    a ≫ f ≫ g = b ≫ f ≫ g := by
  rw [h]

/-- A piece transformation expressed in the common object coordinates of its
source and target descent data. -/
def transportedPieceApp
    (D E : @TwoOpenDescentDatum X _ U V C _)
    {b : Bool}
    (α : D.functor b ⟶ E.functor b)
    (z : FundamentalGroupoid (CoverPiece U V b)) :
    D.obj z.as.1 ⟶ E.obj z.as.1 :=
  eqToHom (D.obj_eq b z).symm ≫ α.app z ≫ eqToHom (E.obj_eq b z)

/-- Compatibility data for a 2-cell on the two cover pieces.  Agreement of
components on overlap objects is the only extra condition: the overlap-path
squares follow from this equality and naturality of the two piece
transformations. -/
structure CompatibleNatTrans
    (D E : @TwoOpenDescentDatum X _ U V C _) where
  piece : (b : Bool) → D.functor b ⟶ E.functor b
  overlap_app : ∀ (x : X) (hU : x ∈ U) (hV : x ∈ V),
    transportedPieceApp D E (piece false)
        (⟨⟨x, by simpa [twoChart] using hV⟩⟩) =
      transportedPieceApp D E (piece true)
        (⟨⟨x, by simpa [twoChart] using hU⟩⟩)

namespace CompatibleNatTrans

variable {D E : @TwoOpenDescentDatum X _ U V C _}

/-- Common-coordinate component supplied by a specified containing chart. -/
def chartApp (τ : CompatibleNatTrans D E) (b : Bool) (x : X)
    (hx : x ∈ twoChart U V b) : D.obj x ⟶ E.obj x :=
  transportedPieceApp D E (τ.piece b) ⟨⟨x, hx⟩⟩

theorem chartApp_false_eq_true (τ : CompatibleNatTrans D E)
    (x : X) (hU : x ∈ U) (hV : x ∈ V) :
    τ.chartApp false x (by simpa [twoChart] using hV) =
      τ.chartApp true x (by simpa [twoChart] using hU) :=
  τ.overlap_app x hU hV

/-- The ambient object component, choosing the first chart when possible and
the second chart otherwise.  The following theorems remove this choice. -/
def ambientApp (hcover : U ∪ V = Set.univ)
    (τ : CompatibleNatTrans D E) (x : X) : D.obj x ⟶ E.obj x := by
  classical
  exact if hU : x ∈ U then
      τ.chartApp true x (by simpa [twoChart] using hU)
    else
      τ.chartApp false x (by
        simpa [twoChart] using
          (show x ∈ V from (by
            have hx : x ∈ U ∪ V := by rw [hcover]; trivial
            exact hx.resolve_left hU)))

theorem ambientApp_eq_true (hcover : U ∪ V = Set.univ)
    (τ : CompatibleNatTrans D E) (x : X) (hU : x ∈ U) :
    τ.ambientApp hcover x =
      τ.chartApp true x (by simpa [twoChart] using hU) := by
  simp [ambientApp, hU]

theorem ambientApp_eq_false (hcover : U ∪ V = Set.univ)
    (τ : CompatibleNatTrans D E) (x : X) (hV : x ∈ V) :
    τ.ambientApp hcover x =
      τ.chartApp false x (by simpa [twoChart] using hV) := by
  by_cases hU : x ∈ U
  · rw [ambientApp_eq_true hcover τ x hU]
    exact τ.chartApp_false_eq_true x hU hV |>.symm
  · unfold ambientApp
    simp only [dif_neg hU]

/-- The candidate component between the two ambient descent functors. -/
def ambientComponent (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (τ : CompatibleNatTrans D E)
    (x : FundamentalGroupoid X) :
    (twoOpenDescentFunctor hU hV hcover D).obj x ⟶
      (twoOpenDescentFunctor hU hV hcover E).obj x :=
  τ.ambientApp hcover x.as

theorem ambientComponent_eq_chart (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (τ : CompatibleNatTrans D E)
    (b : Bool) (z : FundamentalGroupoid (CoverPiece U V b)) :
    τ.ambientComponent hU hV hcover
        ((FundamentalGroupoid.map (coverPieceInclusion b)).obj z) =
      transportedPieceApp D E (τ.piece b) z := by
  cases b
  · exact ambientApp_eq_false hcover τ z.as.1 (by simpa using z.as.2)
  · exact ambientApp_eq_true hcover τ z.as.1 (by simpa using z.as.2)

/-- The former left overlap-path field follows from overlap component
agreement and the descent datum's overlap equality. -/
theorem overlap_map_left (τ : CompatibleNatTrans D E)
    {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V) :
    D.mapPath false p (by simpa [twoChart] using hV) ≫
        transportedPieceApp D E (τ.piece false)
          (⟨⟨y, by simpa [twoChart] using hV 1⟩⟩) =
      D.mapPath true p (by simpa [twoChart] using hU) ≫
        transportedPieceApp D E (τ.piece true)
          (⟨⟨y, by simpa [twoChart] using hU 1⟩⟩) := by
  have hyU : y ∈ U := by simpa using hU 1
  have hyV : y ∈ V := by simpa using hV 1
  rw [D.mapPath_false_eq_true p hU hV, τ.overlap_app y hyU hyV]

/-- The former right overlap-path field is likewise derived, rather than
required as compatibility data. -/
theorem overlap_map_right (τ : CompatibleNatTrans D E)
    {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V) :
    transportedPieceApp D E (τ.piece false)
          (⟨⟨x, by simpa [twoChart] using hV 0⟩⟩) ≫
        E.mapPath false p (by simpa [twoChart] using hV) =
      transportedPieceApp D E (τ.piece true)
          (⟨⟨x, by simpa [twoChart] using hU 0⟩⟩) ≫
        E.mapPath true p (by simpa [twoChart] using hU) := by
  have hxU : x ∈ U := by simpa using hU 0
  have hxV : x ∈ V := by simpa using hV 0
  rw [τ.overlap_app x hxU hxV, E.mapPath_false_eq_true p hU hV]

/-- Naturality on one selected subdivision segment, expressed in the common
ambient object coordinates. -/
theorem mappedPiece_naturality
    (τ : CompatibleNatTrans D E) {x y : X} {p : Path x y}
    (S : PathTwoOpenSubdivision p U V) (k : Fin (S.n + 1)) :
    D.mappedPiece S k ≫
        τ.chartApp (S.side k) (S.point k.succ)
          (by simpa using (S.piece_mem k 1)) =
      τ.chartApp (S.side k) (S.point k.castSucc)
          (by simpa using (S.piece_mem k 0)) ≫
        E.mappedPiece S k := by
  exact transported_naturality _ _ _ _
    ((τ.piece (S.side k)).naturality
      (Path.Homotopic.Quotient.mk
        (pathInPiece U V (S.side k) (S.piece k) (S.piece_mem k))))
    (D.obj_eq _ _) (D.obj_eq _ _) (E.obj_eq _ _) (E.obj_eq _ _)

/-- The naturality squares for all pieces of a subdivision telescope. -/
theorem composeFin_naturality
    (hcover : U ∪ V = Set.univ) (τ : CompatibleNatTrans D E)
    {x y : X} {p : Path x y} (S : PathTwoOpenSubdivision p U V) :
    TwoOpenDescentDatum.composeFin (D.obj ∘ S.point) (D.mappedPiece S) ≫
        τ.ambientApp hcover (S.point (Fin.last (S.n + 1))) =
      τ.ambientApp hcover (S.point 0) ≫
        TwoOpenDescentDatum.composeFin (E.obj ∘ S.point) (E.mappedPiece S) := by
  apply composeFin_ladder (n := S.n + 1)
    (D.obj ∘ S.point) (E.obj ∘ S.point)
    (D.mappedPiece S) (E.mappedPiece S)
    (fun i ↦ τ.ambientApp hcover (S.point i))
  intro k
  cases hs : S.side k
  · rw [τ.ambientApp_eq_false hcover _
        (by simpa [twoChart, hs] using S.piece_mem k 1),
      τ.ambientApp_eq_false hcover _
        (by simpa [twoChart, hs] using S.piece_mem k 0)]
    simpa [hs] using τ.mappedPiece_naturality S k
  · rw [τ.ambientApp_eq_true hcover _
        (by simpa [twoChart, hs] using S.piece_mem k 1),
      τ.ambientApp_eq_true hcover _
        (by simpa [twoChart, hs] using S.piece_mem k 0)]
    simpa [hs] using τ.mappedPiece_naturality S k

/-- Evaluation of every subordinate subdivision is natural for the glued
ambient component. -/
theorem evaluate_naturality
    (hcover : U ∪ V = Set.univ) (τ : CompatibleNatTrans D E)
    {x y : X} {p : Path x y} (S : PathTwoOpenSubdivision p U V) :
    D.evaluate S ≫ τ.ambientApp hcover y =
      τ.ambientApp hcover x ≫ E.evaluate S := by
  let fD := TwoOpenDescentDatum.composeFin
    (D.obj ∘ S.point) (D.mappedPiece S)
  let fE := TwoOpenDescentDatum.composeFin
    (E.obj ∘ S.point) (E.mappedPiece S)
  have hsquare : fD ≫ τ.ambientApp hcover (S.point (Fin.last (S.n + 1))) =
      τ.ambientApp hcover (S.point 0) ≫ fE :=
    τ.composeFin_naturality hcover S
  have hlast := dependent_component_transport_forward D.obj E.obj
    (τ.ambientApp hcover) S.point_last
  have hzero := dependent_component_transport_backward D.obj E.obj
    (τ.ambientApp hcover) S.point_zero
  have hsuffix :
      (fD ≫ τ.ambientApp hcover (S.point (Fin.last (S.n + 1)))) ≫
          eqToHom (congrArg E.obj S.point_last) =
        (τ.ambientApp hcover (S.point 0) ≫ fE) ≫
          eqToHom (congrArg E.obj S.point_last) :=
    congrArg (fun q ↦ q ≫ eqToHom (congrArg E.obj S.point_last)) hsquare
  have hsuffix' :
      fD ≫ τ.ambientApp hcover (S.point (Fin.last (S.n + 1))) ≫
          eqToHom (congrArg E.obj S.point_last) =
        τ.ambientApp hcover (S.point 0) ≫ fE ≫
          eqToHom (congrArg E.obj S.point_last) := by
    simpa only [Category.assoc] using hsuffix
  unfold TwoOpenDescentDatum.evaluate
  change (eqToHom _ ≫ fD ≫ eqToHom _) ≫ τ.ambientApp hcover y =
    τ.ambientApp hcover x ≫ (eqToHom _ ≫ fE ≫ eqToHom _)
  simp only [Category.assoc]
  slice_lhs 3 4 => exact hlast
  slice_lhs 2 4 => exact hsuffix'
  calc
    _ = (eqToHom (congrArg D.obj S.point_zero).symm ≫
          τ.ambientApp hcover (S.point 0)) ≫ fE ≫
          eqToHom (congrArg E.obj S.point_last) := by
        simp only [Category.assoc]
        rfl
    _ = (τ.ambientApp hcover x ≫
          eqToHom (congrArg E.obj S.point_zero).symm) ≫ fE ≫
          eqToHom (congrArg E.obj S.point_last) :=
        whisker_two_of_eq hzero.symm fE _
    _ = _ := by
      simp only [Category.assoc]
      rfl

/-- Naturality on an arbitrary represented ambient path. -/
theorem ambientComponent_naturality_mk
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (τ : CompatibleNatTrans D E) {x y : X} (p : Path x y)
    (S : PathTwoOpenSubdivision p U V) :
    (twoOpenDescentFunctor hU hV hcover D).map
          (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p)) ≫
        τ.ambientComponent hU hV hcover ⟨y⟩ =
      τ.ambientComponent hU hV hcover ⟨x⟩ ≫
        (twoOpenDescentFunctor hU hV hcover E).map
          (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p)) := by
  rw [twoOpenDescentFunctor_map_mk hU hV hcover D p S,
    twoOpenDescentFunctor_map_mk hU hV hcover E p S]
  exact τ.evaluate_naturality hcover S

/-- The ambient natural transformation glued from compatible transformations
on the two cover pieces. -/
def ambientNatTrans
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (τ : CompatibleNatTrans D E) :
    twoOpenDescentFunctor hU hV hcover D ⟶
      twoOpenDescentFunctor hU hV hcover E where
  app := τ.ambientComponent hU hV hcover
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ ⟨p⟩
    exact τ.ambientComponent_naturality_mk hU hV hcover p
      (chosenSubdivision hU hV hcover p)

/-- On each piece, the glued transformation agrees with the supplied one
through the explicit restriction isomorphisms. -/
theorem ambientNatTrans_restriction_app
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (τ : CompatibleNatTrans D E) (b : Bool)
    (z : FundamentalGroupoid (CoverPiece U V b)) :
    (τ.piece b).app z ≫
        (restrictionAppIso hU hV hcover E b z).hom =
      (restrictionAppIso hU hV hcover D b z).hom ≫
        (Functor.whiskerLeft
          (FundamentalGroupoid.map (coverPieceInclusion b))
          (τ.ambientNatTrans hU hV hcover)).app z := by
  change (τ.piece b).app z ≫
        (restrictionAppIso hU hV hcover E b z).hom =
      (restrictionAppIso hU hV hcover D b z).hom ≫
        (τ.ambientNatTrans hU hV hcover).app
          ((FundamentalGroupoid.map (coverPieceInclusion b)).obj z)
  rw [show (τ.ambientNatTrans hU hV hcover).app
      ((FundamentalGroupoid.map (coverPieceInclusion b)).obj z) =
      transportedPieceApp D E (τ.piece b) z from
    τ.ambientComponent_eq_chart hU hV hcover b z]
  unfold restrictionAppIso transportedPieceApp
  exact conjugation_recover _ (D.obj_eq b z) (E.obj_eq b z)

#print axioms transportedPieceApp
#print axioms CompatibleNatTrans
#print axioms CompatibleNatTrans.ambientApp
#print axioms CompatibleNatTrans.ambientApp_eq_true
#print axioms CompatibleNatTrans.ambientApp_eq_false
#print axioms CompatibleNatTrans.ambientComponent_eq_chart
#print axioms CompatibleNatTrans.overlap_map_left
#print axioms CompatibleNatTrans.overlap_map_right
#print axioms CompatibleNatTrans.mappedPiece_naturality
#print axioms CompatibleNatTrans.composeFin_naturality
#print axioms CompatibleNatTrans.evaluate_naturality
#print axioms CompatibleNatTrans.ambientNatTrans
#print axioms CompatibleNatTrans.ambientNatTrans_restriction_app

end CompatibleNatTrans

end ConstructionTargets.TwoOpenDescentFullness
