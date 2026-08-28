import ConstructionTargets.HomotopySquareRowSubdivisions

/-!
# Cell edges in a subordinate homotopy-square grid

This module constructs the vertical grid edges and all four boundary paths of
one grid cell, valued in the cover member assigned to that cell.
-/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.HomotopySquareCellBoundary

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareRowSubdivisions

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}

theorem coord_castSucc_le_succ (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    G.coord i.castSucc ≤ G.coord i.succ := by
  rw [G.coord_eq_grid]
  exact monotone_gridCoord G.N G.N_pos i.castSucc_le_succ

def coordSegment (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N)
    (t : unitInterval) : unitInterval :=
  Icc.convexCombo (G.coord i.castSucc) (G.coord i.succ) t

@[simp] theorem coordSegment_zero (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    coordSegment H G i 0 = G.coord i.castSucc :=
  Icc.convexCombo_zero _ _

@[simp] theorem coordSegment_one (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    coordSegment H G i 1 = G.coord i.succ :=
  Icc.convexCombo_one _ _

theorem coordSegment_mem (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N)
    (t : unitInterval) :
    coordSegment H G i t ∈ Icc (G.coord i.castSucc) (G.coord i.succ) :=
  ⟨Icc.le_convexCombo (coord_castSucc_le_succ H G i) t,
    Icc.convexCombo_le (coord_castSucc_le_succ H G i) t⟩

theorem continuous_coordSegment (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    Continuous (coordSegment H G i) :=
  Icc.continuous_convexCombo _ _

/-- A vertical grid edge.  Its parameter traverses homotopy time, while its
second square coordinate is the fixed path-grid coordinate. -/
def verticalEdge (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (i : Fin G.N) (r : Fin (G.N + 1)) :
    Path (rowPath H G i.castSucc (G.coord r))
      (rowPath H G i.succ (G.coord r)) where
  toFun t := H (coordSegment H G i t, G.coord r)
  continuous_toFun := H.continuous.comp
    ((continuous_coordSegment H G i).prodMk continuous_const)
  source' := by simp [rowPath]
  target' := by simp [rowPath]

@[simp] theorem verticalEdge_apply (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (i : Fin G.N) (r : Fin (G.N + 1)) (t : unitInterval) :
    verticalEdge H G i r t = H (coordSegment H G i t, G.coord r) := rfl

private def cellPointMem (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N)
    (a b : unitInterval)
    (ha : a ∈ Icc (G.coord i.castSucc) (G.coord i.succ))
    (hb : b ∈ Icc (G.coord j.castSucc) (G.coord j.succ)) :
    H (a, b) ∈ twoChart U V (G.side (i, j)) := by
  apply G.cell_mem i j (a, b)
  rw [gridCell]
  constructor
  · simpa only [G.coord_eq_grid] using ha
  · simpa only [G.coord_eq_grid] using hb

theorem verticalEdge_left_mem (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N)
    (t : unitInterval) :
    verticalEdge H G i j.castSucc t ∈ twoChart U V (G.side (i, j)) :=
  cellPointMem H G i j _ _ (coordSegment_mem H G i t)
    ⟨le_rfl, coord_castSucc_le_succ H G j⟩

theorem verticalEdge_right_mem (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N)
    (t : unitInterval) :
    verticalEdge H G i j.succ t ∈ twoChart U V (G.side (i, j)) :=
  cellPointMem H G i j _ _ (coordSegment_mem H G i t)
    ⟨coord_castSucc_le_succ H G j, le_rfl⟩

def cellCorner (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N)
    (upperTime upperPath : Bool) : twoChart U V (G.side (i, j)) :=
  let a := if upperTime then G.coord i.succ else G.coord i.castSucc
  let b := if upperPath then G.coord j.succ else G.coord j.castSucc
  ⟨H (a, b), cellPointMem H G i j a b (by
      cases upperTime <;> simp [a, coord_castSucc_le_succ H G i]) (by
      cases upperPath <;> simp [b, coord_castSucc_le_succ H G j])⟩

def cellBottomEdge (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N) :
    Path (cellCorner H G i j false false) (cellCorner H G i j false true) where
  toFun t := ⟨H (G.coord i.castSucc, coordSegment H G j t),
    cellPointMem H G i j _ _
      ⟨le_rfl, coord_castSucc_le_succ H G i⟩ (coordSegment_mem H G j t)⟩
  continuous_toFun := (H.continuous.comp
    (continuous_const.prodMk (continuous_coordSegment H G j))).subtype_mk _
  source' := by ext; simp [cellCorner]
  target' := by ext; simp [cellCorner]

def cellTopEdge (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N) :
    Path (cellCorner H G i j true false) (cellCorner H G i j true true) where
  toFun t := ⟨H (G.coord i.succ, coordSegment H G j t),
    cellPointMem H G i j _ _
      ⟨coord_castSucc_le_succ H G i, le_rfl⟩ (coordSegment_mem H G j t)⟩
  continuous_toFun := (H.continuous.comp
    (continuous_const.prodMk (continuous_coordSegment H G j))).subtype_mk _
  source' := by ext; simp [cellCorner]
  target' := by ext; simp [cellCorner]

def cellLeftEdge (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N) :
    Path (cellCorner H G i j false false) (cellCorner H G i j true false) where
  toFun t := ⟨H (coordSegment H G i t, G.coord j.castSucc),
    cellPointMem H G i j _ _ (coordSegment_mem H G i t)
      ⟨le_rfl, coord_castSucc_le_succ H G j⟩⟩
  continuous_toFun := (H.continuous.comp
    ((continuous_coordSegment H G i).prodMk continuous_const)).subtype_mk _
  source' := by apply Subtype.ext; simp [cellCorner]
  target' := by apply Subtype.ext; simp [cellCorner]

def cellRightEdge (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N) :
    Path (cellCorner H G i j false true) (cellCorner H G i j true true) where
  toFun t := ⟨H (coordSegment H G i t, G.coord j.succ),
    cellPointMem H G i j _ _ (coordSegment_mem H G i t)
      ⟨coord_castSucc_le_succ H G j, le_rfl⟩⟩
  continuous_toFun := (H.continuous.comp
    ((continuous_coordSegment H G i).prodMk continuous_const)).subtype_mk _
  source' := by apply Subtype.ext; simp [cellCorner]
  target' := by apply Subtype.ext; simp [cellCorner]

@[simp] theorem cellBottomEdge_apply (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N)
    (t : unitInterval) :
    ((cellBottomEdge H G i j t : twoChart U V (G.side (i, j))) : X) =
      H (G.coord i.castSucc, coordSegment H G j t) := rfl

@[simp] theorem cellTopEdge_apply (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N)
    (t : unitInterval) :
    ((cellTopEdge H G i j t : twoChart U V (G.side (i, j))) : X) =
      H (G.coord i.succ, coordSegment H G j t) := rfl

@[simp] theorem cellLeftEdge_apply (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N)
    (t : unitInterval) :
    ((cellLeftEdge H G i j t : twoChart U V (G.side (i, j))) : X) =
      H (coordSegment H G i t, G.coord j.castSucc) := rfl

@[simp] theorem cellRightEdge_apply (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i j : Fin G.N)
    (t : unitInterval) :
    ((cellRightEdge H G i j t : twoChart U V (G.side (i, j))) : X) =
      H (coordSegment H G i t, G.coord j.succ) := rfl

#print axioms verticalEdge
#print axioms verticalEdge_left_mem
#print axioms verticalEdge_right_mem
#print axioms cellBottomEdge
#print axioms cellTopEdge
#print axioms cellLeftEdge
#print axioms cellRightEdge

end ConstructionTargets.HomotopySquareCellBoundary
