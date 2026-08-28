import ConstructionTargets.HomotopySquareStripDescent

/-!
# The vertical family and finite ladder for one homotopy-grid strip
-/

open Set CategoryTheory
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.HomotopySquareStripLadder

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareRowSubdivisions
open ConstructionTargets.HomotopySquareCellBoundary
open ConstructionTargets.HomotopySquareCellDescent
open ConstructionTargets.HomotopySquareStripDescent

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}
variable {C : Type*} [Category C]

def finalCell (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) : Fin G.N :=
  rowSegmentIndex G (Fin.last (rowSubdivisionN G))

theorem finalCell_succ (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) :
    (finalCell H G).succ = Fin.last G.N := by
  apply Fin.ext
  simp [finalCell, rowSegmentIndex, rowSubdivisionN_add_one]

theorem terminalBottomPoint_eq (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    (bottomSubdivision H G i).point (Fin.last (rowSubdivisionN G + 1)) =
      rowPath H G i.castSucc (G.coord (finalCell H G).succ) := by
  change rowPath H G i.castSucc (rowVertex G _) = _
  rw [rowVertex_last, finalCell_succ, G.coord_eq_grid, gridCoord_last]

theorem terminalTopPoint_eq (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    rowPath H G i.succ (G.coord (finalCell H G).succ) =
      (topSubdivision H G i).point (Fin.last (rowSubdivisionN G + 1)) := by
  change _ = rowPath H G i.succ (rowVertex G _)
  rw [rowVertex_last, finalCell_succ, G.coord_eq_grid, gridCoord_last]

def terminalVertical (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    D.obj ((bottomSubdivision H G i).point
        (Fin.last (rowSubdivisionN G + 1))) ⟶
      D.obj ((topSubdivision H G i).point
        (Fin.last (rowSubdivisionN G + 1))) :=
  D.mapPath (G.side (i, finalCell H G))
    (verticalEdge H G i (finalCell H G).succ)
    (verticalEdge_right_mem H G i (finalCell H G))

/-- At a nonterminal row vertex, use the left vertical edge of the following
cell; at the terminal vertex, use the right edge of the final cell. -/
def stripVertical (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    (r : Fin (rowSubdivisionN G + 2)) →
      D.obj ((bottomSubdivision H G i).point r) ⟶
        D.obj ((topSubdivision H G i).point r) :=
  Fin.lastCases (terminalVertical H G D i) (fun j ↦
    D.mapPath (G.side (i, rowSegmentIndex G j))
      (verticalEdge H G i (rowSegmentIndex G j).castSucc)
      (verticalEdge_left_mem H G i (rowSegmentIndex G j)))

@[simp] theorem stripVertical_castSucc (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N)
    (j : Fin (rowSubdivisionN G + 1)) :
    stripVertical H G D i j.castSucc =
      D.mapPath (G.side (i, rowSegmentIndex G j))
        (verticalEdge H G i (rowSegmentIndex G j).castSucc)
        (verticalEdge_left_mem H G i (rowSegmentIndex G j)) := by
  simp [stripVertical]
  congr

@[simp] theorem stripVertical_last (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    stripVertical H G D i (Fin.last (rowSubdivisionN G + 1)) =
      terminalVertical H G D i := by
  simp [stripVertical]

theorem stripVertical_succ_eq_right (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N)
    (j : Fin (rowSubdivisionN G + 1)) :
    stripVertical H G D i j.succ =
      D.mapPath (G.side (i, rowSegmentIndex G j))
        (verticalEdge H G i (rowSegmentIndex G j).succ)
        (verticalEdge_right_mem H G i (rowSegmentIndex G j)) := by
  by_cases hlast : j = Fin.last (rowSubdivisionN G)
  · subst j
    change stripVertical H G D i (Fin.last (rowSubdivisionN G + 1)) = _
    rw [stripVertical_last]
    rfl
  · have hj : j.val + 1 < rowSubdivisionN G + 1 := by
      have hjlt := j.isLt
      have hval : j.val ≠ rowSubdivisionN G := by
        intro h
        apply hlast
        apply Fin.ext
        simpa using h
      omega
    let k : Fin (rowSubdivisionN G + 1) := ⟨j.val + 1, hj⟩
    change stripVertical H G D i k.castSucc = _
    rw [stripVertical_castSucc]
    symm
    apply shared_vertical_mapPath_eq H G D i
    apply Fin.ext
    rfl

@[simp] theorem rowSegmentOfCell_rowSegmentIndex (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (j : Fin (rowSubdivisionN G + 1)) :
    rowSegmentOfCell G (rowSegmentIndex G j) = j := by
  apply Fin.ext
  rfl

/-- The cell squares telescope across a fixed time strip. -/
theorem strip_composeFin_square (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    TwoOpenDescentDatum.composeFin
          (D.obj ∘ (bottomSubdivision H G i).point)
          (D.mappedPiece (bottomSubdivision H G i)) ≫
        stripVertical H G D i (Fin.last (rowSubdivisionN G + 1)) =
      stripVertical H G D i 0 ≫
        TwoOpenDescentDatum.composeFin
          (D.obj ∘ (topSubdivision H G i).point)
          (D.mappedPiece (topSubdivision H G i)) := by
  refine composeFin_ladder (n := rowSubdivisionN G + 1)
    (D.obj ∘ (bottomSubdivision H G i).point)
    (D.obj ∘ (topSubdivision H G i).point)
    (D.mappedPiece (bottomSubdivision H G i))
    (D.mappedPiece (topSubdivision H G i))
    (stripVertical H G D i) ?_
  intro j
  rw [stripVertical_succ_eq_right H G D i j,
    stripVertical_castSucc H G D i j]
  simpa only [rowSegmentOfCell_rowSegmentIndex] using
    normalized_cell_square H G D i (rowSegmentIndex G j)

#print axioms stripVertical_castSucc
#print axioms stripVertical_last
#print axioms stripVertical_succ_eq_right
#print axioms strip_composeFin_square

end ConstructionTargets.HomotopySquareStripLadder
