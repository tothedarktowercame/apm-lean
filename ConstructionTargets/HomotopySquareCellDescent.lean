import ConstructionTargets.HomotopySquareCellBoundary
import ConstructionTargets.FundamentalGroupoidTwoOpenRefinement

/-!
# Descent morphisms around a labelled homotopy-grid cell
-/

open Set CategoryTheory
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.HomotopySquareCellDescent

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidTwoOpenRefinement
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareRowSubdivisions
open ConstructionTargets.HomotopySquareCellBoundary

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}
variable {C : Type*} [Category C]

def ambientPiecePath {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) : Path (a : X) (z : X) :=
  r.map continuous_subtype_val

@[simp] theorem ambientPiecePath_apply {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) (t : unitInterval) : ambientPiecePath r t = r t := rfl

theorem ambientPiecePath_mem {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) (t : unitInterval) :
    ambientPiecePath r t ∈ twoChart U V b := (r t).property

theorem pathInPiece_ambientPiecePath {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) :
    pathInPiece U V b (ambientPiecePath r) (ambientPiecePath_mem r) = r := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

theorem mapPath_ambientPiecePath
    (D : @TwoOpenDescentDatum X _ U V C _) {b : Bool}
    {a z : CoverPiece U V b} (r : Path a z) :
    D.mapPath b (ambientPiecePath r) (ambientPiecePath_mem r) =
      eqToHom (D.obj_eq b (FundamentalGroupoid.mk a)).symm ≫
        (D.functor b).map (Path.Homotopic.Quotient.mk r) ≫
        eqToHom (D.obj_eq b (FundamentalGroupoid.mk z)) := by
  simp only [TwoOpenDescentDatum.mapPath]
  rw [pathInPiece_ambientPiecePath]

def bottomRightAmbientMem (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N) :
    ∀ t, ((ambientPiecePath (cellBottomEdge H G i j)).trans
      (ambientPiecePath (cellRightEdge H G i j))) t ∈
        twoChart U V (G.side (i, j)) := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact ambientPiecePath_mem _ _
  · exact ambientPiecePath_mem _ _

def leftTopAmbientMem (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N) :
    ∀ t, ((ambientPiecePath (cellLeftEdge H G i j)).trans
      (ambientPiecePath (cellTopEdge H G i j))) t ∈
        twoChart U V (G.side (i, j)) := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact ambientPiecePath_mem _ _
  · exact ambientPiecePath_mem _ _

/-- The common-coordinate descent square supplied by one labelled grid cell. -/
theorem cell_mapPath_square (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i j : Fin G.N) :
    D.mapPath (G.side (i, j)) (ambientPiecePath (cellBottomEdge H G i j))
          (ambientPiecePath_mem _) ≫
        D.mapPath (G.side (i, j)) (ambientPiecePath (cellRightEdge H G i j))
          (ambientPiecePath_mem _) =
      D.mapPath (G.side (i, j)) (ambientPiecePath (cellLeftEdge H G i j))
          (ambientPiecePath_mem _) ≫
        D.mapPath (G.side (i, j)) (ambientPiecePath (cellTopEdge H G i j))
          (ambientPiecePath_mem _) := by
  rw [← FundamentalGroupoidTwoOpenRefinement.TwoOpenDescentDatum.mapPath_trans D,
    ← FundamentalGroupoidTwoOpenRefinement.TwoOpenDescentDatum.mapPath_trans D]
  simp only [TwoOpenDescentDatum.mapPath]
  have hbr :
      pathInPiece U V (G.side (i, j))
          ((ambientPiecePath (cellBottomEdge H G i j)).trans
            (ambientPiecePath (cellRightEdge H G i j)))
            (bottomRightAmbientMem H G i j) =
        (cellBottomEdge H G i j).trans (cellRightEdge H G i j) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change ((ambientPiecePath (cellBottomEdge H G i j)).trans
      (ambientPiecePath (cellRightEdge H G i j))) t =
        ↑(((cellBottomEdge H G i j).trans (cellRightEdge H G i j)) t)
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  have hlt :
      pathInPiece U V (G.side (i, j))
          ((ambientPiecePath (cellLeftEdge H G i j)).trans
            (ambientPiecePath (cellTopEdge H G i j)))
            (leftTopAmbientMem H G i j) =
        (cellLeftEdge H G i j).trans (cellTopEdge H G i j) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change ((ambientPiecePath (cellLeftEdge H G i j)).trans
      (ambientPiecePath (cellTopEdge H G i j))) t =
        ↑(((cellLeftEdge H G i j).trans (cellTopEdge H G i j)) t)
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  rw [hbr, hlt]
  simpa only using congrArg
    (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _)
    (cellEdgeBoundary_piece_map_eq H G D i j)

/-- A vertical edge in common object coordinates, using the label of a cell
on its right. -/
def verticalMorphism (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _)
    (i j : Fin G.N) :
    D.obj (rowPath H G i.castSucc (G.coord j.castSucc)) ⟶
      D.obj (rowPath H G i.succ (G.coord j.castSucc)) :=
  D.mapPath (G.side (i, j)) (verticalEdge H G i j.castSucc)
    (verticalEdge_left_mem H G i j)

/-- The two labels of adjacent cells assign the same common-coordinate
morphism to their shared vertical edge.  The equality `hjk` records that the
right vertex of `j` is the left vertex of `k`; no arithmetic presentation of
the adjacent indices is built into the theorem. -/
theorem shared_vertical_mapPath_eq (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _)
    (i j k : Fin G.N) (hjk : j.succ = k.castSucc) :
    D.mapPath (G.side (i, j)) (verticalEdge H G i j.succ)
        (verticalEdge_right_mem H G i j) =
      D.mapPath (G.side (i, k)) (verticalEdge H G i j.succ) (by
        intro t
        rw [hjk]
        exact verticalEdge_left_mem H G i k t) := by
  have hright := verticalEdge_right_mem H G i j
  have hleft : ∀ t, verticalEdge H G i j.succ t ∈
      twoChart U V (G.side (i, k)) := by
    intro t
    rw [hjk]
    exact verticalEdge_left_mem H G i k t
  by_cases hs : G.side (i, j) = G.side (i, k)
  · simpa only [hs]
  · have hcases :
        (G.side (i, j) = false ∧ G.side (i, k) = true) ∨
          (G.side (i, j) = true ∧ G.side (i, k) = false) := by
      rcases Bool.eq_false_or_eq_true (G.side (i, j)) with hj | hj <;>
        rcases Bool.eq_false_or_eq_true (G.side (i, k)) with hk | hk
      · exact False.elim (hs (hj.trans hk.symm))
      · exact Or.inr ⟨hj, hk⟩
      · exact Or.inl ⟨hj, hk⟩
      · exact False.elim (hs (hj.trans hk.symm))
    rcases hcases with ⟨hj, hk⟩ | ⟨hj, hk⟩
    · have heq := D.mapPath_false_eq_true (verticalEdge H G i j.succ)
          (fun t ↦ by simpa [twoChart, hk] using hleft t)
          (fun t ↦ by simpa [twoChart, hj] using hright t)
      simpa only [hj, hk] using heq
    · have heq := (D.mapPath_false_eq_true (verticalEdge H G i j.succ)
          (fun t ↦ by simpa [twoChart, hj] using hright t)
          (fun t ↦ by simpa [twoChart, hk] using hleft t)).symm
      simpa only [hj, hk] using heq

#print axioms cell_mapPath_square
#print axioms shared_vertical_mapPath_eq

end ConstructionTargets.HomotopySquareCellDescent
