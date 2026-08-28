import ConstructionTargets.TwoOpenDescentUniqueness

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
open ConstructionTargets.TwoOpenDescentRestriction
open ConstructionTargets.TwoOpenDescentFunctor

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- A piece transformation expressed in the common object coordinates of its
source and target descent data. -/
def transportedPieceApp
    (D E : @TwoOpenDescentDatum X _ U V C _)
    {b : Bool}
    (α : D.functor b ⟶ E.functor b)
    (z : FundamentalGroupoid (CoverPiece U V b)) :
    D.obj z.as.1 ⟶ E.obj z.as.1 :=
  eqToHom (D.obj_eq b z).symm ≫ α.app z ≫ eqToHom (E.obj_eq b z)

/-- Compatibility data for a 2-cell on the two cover pieces.  Besides its two
natural transformations, it records agreement after transporting to the
common object coordinates, both on overlap objects and on the two orientations
of every overlap path naturality square. -/
structure CompatibleNatTrans
    (D E : @TwoOpenDescentDatum X _ U V C _) where
  piece : (b : Bool) → D.functor b ⟶ E.functor b
  overlap_app : ∀ (x : X) (hU : x ∈ U) (hV : x ∈ V),
    transportedPieceApp D E (piece false)
        (⟨⟨x, by simpa [twoChart] using hV⟩⟩) =
      transportedPieceApp D E (piece true)
        (⟨⟨x, by simpa [twoChart] using hU⟩⟩)
  overlap_map_left : ∀ {x y : X} (p : Path x y)
      (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V),
    D.mapPath false p (by simpa [twoChart] using hV) ≫
        transportedPieceApp D E (piece false)
          (⟨⟨y, by simpa [twoChart] using hV 1⟩⟩) =
      D.mapPath true p (by simpa [twoChart] using hU) ≫
        transportedPieceApp D E (piece true)
          (⟨⟨y, by simpa [twoChart] using hU 1⟩⟩)
  overlap_map_right : ∀ {x y : X} (p : Path x y)
      (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V),
    transportedPieceApp D E (piece false)
          (⟨⟨x, by simpa [twoChart] using hV 0⟩⟩) ≫
        E.mapPath false p (by simpa [twoChart] using hV) =
      transportedPieceApp D E (piece true)
          (⟨⟨x, by simpa [twoChart] using hU 0⟩⟩) ≫
        E.mapPath true p (by simpa [twoChart] using hU)

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

#print axioms transportedPieceApp
#print axioms CompatibleNatTrans
#print axioms CompatibleNatTrans.ambientApp
#print axioms CompatibleNatTrans.ambientApp_eq_true
#print axioms CompatibleNatTrans.ambientApp_eq_false
#print axioms CompatibleNatTrans.ambientComponent_eq_chart

end CompatibleNatTrans

end ConstructionTargets.TwoOpenDescentFullness
