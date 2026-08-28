import ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision

/-!
# Descent evaluation for a two-open path subdivision

This file packages strict object coordinates for two functors out of the
fundamental groupoids of the cover pieces, and evaluates a subordinate path
subdivision as an ordered categorical composite.
-/

open Set CategoryTheory
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidTwoOpenDescent

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision

variable {X : Type*} [TopologicalSpace X] (U V : Set X)
variable {C : Type*} [Category C]

abbrev CoverPiece (b : Bool) := {x : X // x ∈ twoChart U V b}

/-- A path regarded as a path in one member of the cover. -/
def pathInPiece (b : Bool) {x y : X} (p : Path x y)
    (hp : ∀ t, p t ∈ twoChart U V b) :
    Path (⟨x, by simpa using hp 0⟩ : CoverPiece U V b)
      (⟨y, by simpa using hp 1⟩ : CoverPiece U V b) where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- Two piece functors with a common, explicitly chosen object coordinate.
The final field is the precise overlap compatibility needed when a refined
segment can be labelled by either member of the cover. -/
structure TwoOpenDescentDatum where
  obj : X → C
  functor : (b : Bool) → FundamentalGroupoid (CoverPiece U V b) ⥤ C
  obj_eq : ∀ b z, (functor b).obj z = obj z.1
  overlap_eq : ∀ {x y : X} (p : Path x y)
      (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V),
    eqToHom (obj_eq false ⟨x, by simpa [twoChart] using hV 0⟩).symm ≫
        (functor false).map (Path.Homotopic.Quotient.mk
          (pathInPiece U V false p (by simpa [twoChart] using hV))) ≫
        eqToHom (obj_eq false ⟨y, by simpa [twoChart] using hV 1⟩) =
      eqToHom (obj_eq true ⟨x, by simpa [twoChart] using hU 0⟩).symm ≫
        (functor true).map (Path.Homotopic.Quotient.mk
          (pathInPiece U V true p (by simpa [twoChart] using hU))) ≫
        eqToHom (obj_eq true ⟨y, by simpa [twoChart] using hU 1⟩)

namespace TwoOpenDescentDatum

variable {U V} (D : @TwoOpenDescentDatum X _ U V C _)

/-- The morphism assigned to an ambient path contained in one cover member,
transported to the common object coordinate. -/
def mapPath (b : Bool) {x y : X} (p : Path x y)
    (hp : ∀ t, p t ∈ twoChart U V b) : D.obj x ⟶ D.obj y :=
  eqToHom (D.obj_eq b ⟨x, by simpa using hp 0⟩).symm ≫
    (D.functor b).map (Path.Homotopic.Quotient.mk (pathInPiece U V b p hp)) ≫
    eqToHom (D.obj_eq b ⟨y, by simpa using hp 1⟩)

/-- Overlap compatibility in the common object coordinate. -/
theorem mapPath_false_eq_true {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V) :
    D.mapPath false p (by simpa [twoChart] using hV) =
      D.mapPath true p (by simpa [twoChart] using hU) :=
  D.overlap_eq p hU hV

/-- Finite ordered categorical composition, in the same order as `Path.concat`. -/
def composeFin {n : ℕ} (A : Fin (n + 1) → C)
    (f : (k : Fin n) → A k.castSucc ⟶ A k.succ) :
    A 0 ⟶ A (Fin.last n) :=
  Fin.dfoldl n (fun i => A 0 ⟶ A i) (fun i g => g ≫ f i) (𝟙 _)

@[simp] theorem composeFin_zero (A : Fin 1 → C) (f) :
    composeFin A f = 𝟙 _ := by
  simp [composeFin]

theorem composeFin_succ {n : ℕ} (A : Fin (n + 2) → C)
    (f : (k : Fin (n + 1)) → A k.castSucc ⟶ A k.succ) :
    composeFin A f =
      composeFin (A ∘ Fin.castSucc) (fun k => f k.castSucc) ≫ f (Fin.last n) := by
  rw [composeFin, Fin.dfoldl_succ_last]
  rfl

variable {x y : X} {p : Path x y}

/-- The selected cover functor applied to one subdivision piece. -/
def mappedPiece (S : PathTwoOpenSubdivision p U V) (k : Fin (S.n + 1)) :
    D.obj (S.point k.castSucc) ⟶ D.obj (S.point k.succ) :=
  D.mapPath (S.side k) (S.piece k) (S.piece_mem k)

/-- Ordered evaluation of a subordinate subdivision. -/
def evaluate (S : PathTwoOpenSubdivision p U V) :
    D.obj x ⟶ D.obj y :=
  eqToHom (congrArg D.obj S.point_zero).symm ≫
    composeFin (D.obj ∘ S.point) (D.mappedPiece S) ≫
    eqToHom (congrArg D.obj S.point_last)

/-- Replacing the label of a piece whose path lies in the overlap does not
change its assigned morphism. This is the local coherence required by a common
refinement. -/
theorem mappedPiece_label_independent
    (S : PathTwoOpenSubdivision p U V) (k : Fin (S.n + 1))
    (hU : ∀ t, S.piece k t ∈ U) (hV : ∀ t, S.piece k t ∈ V) :
    D.mapPath false (S.piece k) (by simpa [twoChart] using hV) =
      D.mapPath true (S.piece k) (by simpa [twoChart] using hU) :=
  D.mapPath_false_eq_true (S.piece k) hU hV

#print axioms TwoOpenDescentDatum.mapPath_false_eq_true
#print axioms TwoOpenDescentDatum.composeFin_succ
#print axioms TwoOpenDescentDatum.mappedPiece_label_independent

end TwoOpenDescentDatum

end ConstructionTargets.FundamentalGroupoidTwoOpenDescent
