import ConstructionTargets.FundamentalGroupoidTwoOpenDescent

/-!
# Invariance under changing overlap labels
-/

open Set CategoryTheory
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.PathSubdivisionLabelChangeInvariance

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}
variable {C : Type*} [Category C]

/-- Change only the cover labels of a subdivision, retaining its vertex data. -/
def relabelSubdivision (S : PathTwoOpenSubdivision p U V)
    (side : Fin (S.n + 1) → Bool)
    (segment_mem : ∀ k, Icc (S.vertex k.castSucc) (S.vertex k.succ) ⊆
      p ⁻¹' twoChart U V (side k)) : PathTwoOpenSubdivision p U V where
  n := S.n
  vertex := S.vertex
  side := side
  vertex_zero := S.vertex_zero
  vertex_last := S.vertex_last
  monotone_vertex := S.monotone_vertex
  segment_mem := segment_mem

@[simp] theorem relabelSubdivision_vertex
    (S : PathTwoOpenSubdivision p U V) (side) (hmem) :
    (relabelSubdivision S side hmem).vertex = S.vertex := rfl

@[simp] theorem relabelSubdivision_point
    (S : PathTwoOpenSubdivision p U V) (side) (hmem) :
    (relabelSubdivision S side hmem).point = S.point := rfl

@[simp] theorem relabelSubdivision_piece
    (S : PathTwoOpenSubdivision p U V) (side) (hmem) (k : Fin (S.n + 1)) :
    (relabelSubdivision S side hmem).piece k = S.piece k := rfl

@[simp] theorem relabelSubdivision_side
    (S : PathTwoOpenSubdivision p U V) (side) (hmem) (k : Fin (S.n + 1)) :
    (relabelSubdivision S side hmem).side k = side k := rfl

namespace LabelChange

variable (D : @TwoOpenDescentDatum X _ U V C _)

theorem mapPath_label_eq {b b' : Bool} {a z : X} (q : Path a z)
    (h : b = b') (hq : ∀ t, q t ∈ twoChart U V b)
    (hq' : ∀ t, q t ∈ twoChart U V b') :
    D.mapPath b q hq = D.mapPath b' q hq' := by
  subst b'
  congr

/-- `composeFin` respects pointwise equality of its arrows. -/
theorem composeFin_congr {n : ℕ} (A : Fin (n + 1) → C)
    (f g : (k : Fin n) → A k.castSucc ⟶ A k.succ)
    (h : ∀ k, f k = g k) :
    FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin A f =
      FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin A g := by
  congr 1
  funext k
  exact h k

/-- The mapped morphism of a relabelled segment is unchanged when a changed
label is justified by membership in both cover pieces. -/
theorem mappedPiece_relabel_eq
    (S : PathTwoOpenSubdivision p U V)
    (side : Fin (S.n + 1) → Bool)
    (hmem : ∀ k, Icc (S.vertex k.castSucc) (S.vertex k.succ) ⊆
      p ⁻¹' twoChart U V (side k))
    (hoverlap : ∀ k, S.side k ≠ side k →
      (∀ t, S.piece k t ∈ U) ∧ (∀ t, S.piece k t ∈ V))
    (k : Fin (S.n + 1)) :
    D.mappedPiece (relabelSubdivision S side hmem) k = D.mappedPiece S k := by
  change D.mapPath (side k) (S.piece k) _ =
    D.mapPath (S.side k) (S.piece k) _
  by_cases hs : S.side k = side k
  · exact mapPath_label_eq D _ hs.symm _ _
  · have hb := hoverlap k hs
    by_cases hside : side k = false
    · have hS : S.side k = true := by
        cases h : S.side k
        · exact (hs (h.trans hside.symm)).elim
        · rfl
      calc
        _ = D.mapPath false (S.piece k) (by simpa [twoChart] using hb.2) :=
          mapPath_label_eq D _ hside _ _
        _ = D.mapPath true (S.piece k) (by simpa [twoChart] using hb.1) :=
          D.mapPath_false_eq_true (S.piece k) hb.1 hb.2
        _ = _ := mapPath_label_eq D _ hS.symm _ _
    · have hside' : side k = true := by simpa using hside
      have hS : S.side k = false := by
        cases h : S.side k
        · rfl
        · exact (hs (h.trans hside'.symm)).elim
      calc
        _ = D.mapPath true (S.piece k) (by simpa [twoChart] using hb.1) :=
          mapPath_label_eq D _ hside' _ _
        _ = D.mapPath false (S.piece k) (by simpa [twoChart] using hb.2) :=
          (D.mapPath_false_eq_true (S.piece k) hb.1 hb.2).symm
        _ = _ := mapPath_label_eq D _ hS.symm _ _

/-- Evaluation is invariant under changing only labels of overlap-contained
segments.  Membership in both pieces is an explicit hypothesis whenever the
labels differ. -/
theorem evaluate_relabel_eq
    (S : PathTwoOpenSubdivision p U V)
    (side : Fin (S.n + 1) → Bool)
    (hmem : ∀ k, Icc (S.vertex k.castSucc) (S.vertex k.succ) ⊆
      p ⁻¹' twoChart U V (side k))
    (hoverlap : ∀ k, S.side k ≠ side k →
      (∀ t, S.piece k t ∈ U) ∧ (∀ t, S.piece k t ∈ V)) :
    D.evaluate (relabelSubdivision S side hmem) = D.evaluate S := by
  unfold FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.evaluate
  change eqToHom (congrArg D.obj S.point_zero).symm ≫
      FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin
        (D.obj ∘ S.point) (D.mappedPiece (relabelSubdivision S side hmem)) ≫
      eqToHom (congrArg D.obj S.point_last) =
    eqToHom (congrArg D.obj S.point_zero).symm ≫
      FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.composeFin
        (D.obj ∘ S.point) (D.mappedPiece S) ≫
      eqToHom (congrArg D.obj S.point_last)
  have hc := composeFin_congr (D.obj ∘ S.point)
    (D.mappedPiece (relabelSubdivision S side hmem)) (D.mappedPiece S)
    (mappedPiece_relabel_eq D S side hmem hoverlap)
  rw [hc]

#print axioms composeFin_congr
#print axioms mappedPiece_relabel_eq
#print axioms evaluate_relabel_eq

end LabelChange

end ConstructionTargets.PathSubdivisionLabelChangeInvariance
