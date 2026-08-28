import ConstructionTargets.HomotopySquareCellDescent
import ConstructionTargets.PathMapPathTransport

/-!
# Horizontal grid-cell maps and strip descent
-/

open Set CategoryTheory
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.HomotopySquareStripDescent

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareRowSubdivisions
open ConstructionTargets.HomotopySquareCellBoundary
open ConstructionTargets.HomotopySquareCellDescent

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}
variable {C : Type*} [Category C]

/-- A grid-cell column regarded as the segment index of a row subdivision. -/
def rowSegmentOfCell {F : C(unitInterval × unitInterval, X)}
    (G : HomotopySquareGrid F U V) (j : Fin G.N) :
    Fin (rowSubdivisionN G + 1) :=
  Fin.cast (rowSubdivisionN_add_one G).symm j

@[simp] theorem rowSegmentIndex_rowSegmentOfCell
    {F : C(unitInterval × unitInterval, X)}
    (G : HomotopySquareGrid F U V) (j : Fin G.N) :
    rowSegmentIndex G (rowSegmentOfCell G j) = j := by
  apply Fin.ext
  rfl

theorem rowVertex_rowSegmentOfCell_castSucc
    {F : C(unitInterval × unitInterval, X)}
    (G : HomotopySquareGrid F U V) (j : Fin G.N) :
    rowVertex G (rowSegmentOfCell G j).castSucc = G.coord j.castSucc := by
  apply Subtype.ext
  rfl

theorem rowVertex_rowSegmentOfCell_succ
    {F : C(unitInterval × unitInterval, X)}
    (G : HomotopySquareGrid F U V) (j : Fin G.N) :
    rowVertex G (rowSegmentOfCell G j).succ = G.coord j.succ := by
  apply Subtype.ext
  rfl

theorem bottomEdge_ambient_eq_piece (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N) :
    ambientPiecePath (cellBottomEdge H G i j) =
      (bottomSubdivision H G i).piece (rowSegmentOfCell G j) := by
  apply Path.ext
  funext t
  change H (G.coord i.castSucc, coordSegment H G j t) =
    H (G.coord i.castSucc,
      Icc.convexCombo
        (rowVertex G (rowSegmentOfCell G j).castSucc)
        (rowVertex G (rowSegmentOfCell G j).succ) t)
  rw [rowVertex_rowSegmentOfCell_castSucc, rowVertex_rowSegmentOfCell_succ]
  rfl

theorem topEdge_ambient_eq_piece (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N) :
    ambientPiecePath (cellTopEdge H G i j) =
      (topSubdivision H G i).piece (rowSegmentOfCell G j) := by
  apply Path.ext
  funext t
  change H (G.coord i.succ, coordSegment H G j t) =
    H (G.coord i.succ,
      Icc.convexCombo
        (rowVertex G (rowSegmentOfCell G j).castSucc)
        (rowVertex G (rowSegmentOfCell G j).succ) t)
  rw [rowVertex_rowSegmentOfCell_castSucc, rowVertex_rowSegmentOfCell_succ]
  rfl

theorem bottom_mappedPiece_eq_cellMap (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i j : Fin G.N) :
    D.mappedPiece (bottomSubdivision H G i) (rowSegmentOfCell G j) =
      D.mapPath (G.side (i, j)) (ambientPiecePath (cellBottomEdge H G i j))
        (ambientPiecePath_mem _) := by
  simp only [TwoOpenDescentDatum.mappedPiece, bottomSubdivision_side,
    rowSegmentIndex_rowSegmentOfCell]
  have hpath := bottomEdge_ambient_eq_piece H G i j
  cases hpath
  rfl

theorem top_mappedPiece_eq_cellMap (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i j : Fin G.N) :
    D.mappedPiece (topSubdivision H G i) (rowSegmentOfCell G j) =
      D.mapPath (G.side (i, j)) (ambientPiecePath (cellTopEdge H G i j))
        (ambientPiecePath_mem _) := by
  simp only [TwoOpenDescentDatum.mappedPiece, topSubdivision_side,
    rowSegmentIndex_rowSegmentOfCell]
  have hpath := topEdge_ambient_eq_piece H G i j
  cases hpath
  rfl

/-- One cell square with its horizontal sides expressed as the actual mapped
pieces of the two row subdivisions. -/
theorem normalized_cell_square (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i j : Fin G.N) :
    D.mappedPiece (bottomSubdivision H G i) (rowSegmentOfCell G j) ≫
        D.mapPath (G.side (i, j)) (verticalEdge H G i j.succ)
          (verticalEdge_right_mem H G i j) =
      D.mapPath (G.side (i, j)) (verticalEdge H G i j.castSucc)
          (verticalEdge_left_mem H G i j) ≫
        D.mappedPiece (topSubdivision H G i) (rowSegmentOfCell G j) := by
  rw [bottom_mappedPiece_eq_cellMap, top_mappedPiece_eq_cellMap]
  exact cell_mapPath_square H G D i j

/-- A finite ladder of commuting squares telescopes to its two outside
vertical maps. -/
theorem composeFin_ladder {n : ℕ} (A B : Fin (n + 1) → C)
    (bottom : (j : Fin n) → A j.castSucc ⟶ A j.succ)
    (top : (j : Fin n) → B j.castSucc ⟶ B j.succ)
    (vertical : (j : Fin (n + 1)) → A j ⟶ B j)
    (hsquare : ∀ j, bottom j ≫ vertical j.succ =
      vertical j.castSucc ≫ top j) :
    TwoOpenDescentDatum.composeFin A bottom ≫ vertical (Fin.last n) =
      vertical 0 ≫ TwoOpenDescentDatum.composeFin B top := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [TwoOpenDescentDatum.composeFin_succ,
        TwoOpenDescentDatum.composeFin_succ]
      change ((TwoOpenDescentDatum.composeFin (A ∘ Fin.castSucc)
          (fun k ↦ bottom k.castSucc)) ≫ bottom (Fin.last n)) ≫
          vertical (Fin.last n).succ = _
      slice_lhs 2 3 => exact hsquare (Fin.last n)
      have hprefix := ih (A ∘ Fin.castSucc) (B ∘ Fin.castSucc)
          (fun j ↦ bottom j.castSucc) (fun j ↦ top j.castSucc)
          (fun j ↦ vertical j.castSucc) (fun j ↦ hsquare j.castSucc)
      have hsuffix := congrArg (fun k ↦ k ≫ top (Fin.last n)) hprefix
      calc
        _ = ((TwoOpenDescentDatum.composeFin (A ∘ Fin.castSucc)
              (fun j ↦ bottom j.castSucc)) ≫ vertical (Fin.last n).castSucc) ≫
                top (Fin.last n) := (Category.assoc _ _ _).symm
        _ = (vertical (Fin.castSucc 0) ≫
              TwoOpenDescentDatum.composeFin (B ∘ Fin.castSucc)
                (fun j ↦ top j.castSucc)) ≫ top (Fin.last n) := hsuffix
        _ = _ := Category.assoc _ _ _

#print axioms bottomEdge_ambient_eq_piece
#print axioms topEdge_ambient_eq_piece
#print axioms bottom_mappedPiece_eq_cellMap
#print axioms top_mappedPiece_eq_cellMap
#print axioms normalized_cell_square
#print axioms composeFin_ladder

end ConstructionTargets.HomotopySquareStripDescent
