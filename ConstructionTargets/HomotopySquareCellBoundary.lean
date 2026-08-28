import ConstructionTargets.HomotopySquareRowSubdivisions
import ConstructionTargets.FundamentalGroupoidTwoOpenDescent

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
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent

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

/-- Convex interpolation in the unit interval. -/
def intervalLerp (a b t : unitInterval) : unitInterval :=
  ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ), by
    constructor <;> nlinarith [a.2.1, a.2.2, b.2.1, b.2.2, t.2.1, t.2.2]⟩

@[simp] theorem intervalLerp_zero (a b : unitInterval) :
    intervalLerp a b 0 = a := by ext; simp [intervalLerp]

@[simp] theorem intervalLerp_one (a b : unitInterval) :
    intervalLerp a b 1 = b := by ext; simp [intervalLerp]

@[simp] theorem intervalLerp_self (a t : unitInterval) :
    intervalLerp a a t = a := by
  apply Subtype.ext
  simp [intervalLerp]
  ring

theorem intervalLerp_mem_Icc {a b lo hi t : unitInterval}
    (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) :
    intervalLerp a b t ∈ Icc lo hi := by
  constructor
  · change (lo : ℝ) ≤ (intervalLerp a b t : unitInterval)
    change (lo : ℝ) ≤ (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)
    calc
      (lo : ℝ) = (1 - (t : ℝ)) * lo + (t : ℝ) * lo := by ring
      _ ≤ (1 - (t : ℝ)) * a + (t : ℝ) * b :=
        add_le_add (mul_le_mul_of_nonneg_left ha.1 (by linarith [t.2.2]))
          (mul_le_mul_of_nonneg_left hb.1 t.2.1)
  · change (intervalLerp a b t : unitInterval) ≤ (hi : ℝ)
    change (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) ≤ (hi : ℝ)
    calc
      (1 - (t : ℝ)) * a + (t : ℝ) * b ≤
          (1 - (t : ℝ)) * hi + (t : ℝ) * hi :=
        add_le_add (mul_le_mul_of_nonneg_left ha.2 (by linarith [t.2.2]))
          (mul_le_mul_of_nonneg_left hb.2 t.2.1)
      _ = (hi : ℝ) := by ring

/-- The straight path between two unit-interval parameters. -/
def intervalPath (a b : unitInterval) : Path a b where
  toFun := fun t ↦ intervalLerp a b t
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous fun t : unitInterval ↦
      (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)
    fun_prop
  source' := intervalLerp_zero a b
  target' := intervalLerp_one a b

variable {F : C(unitInterval × unitInterval, X)}
  (G : HomotopySquareGrid F U V)

def cell00 (i j : Fin G.N) : unitInterval × unitInterval :=
  (G.coord i.castSucc, G.coord j.castSucc)
def cell01 (i j : Fin G.N) : unitInterval × unitInterval :=
  (G.coord i.castSucc, G.coord j.succ)
def cell10 (i j : Fin G.N) : unitInterval × unitInterval :=
  (G.coord i.succ, G.coord j.castSucc)
def cell11 (i j : Fin G.N) : unitInterval × unitInterval :=
  (G.coord i.succ, G.coord j.succ)

def bottomCoordEdge (i j : Fin G.N) : Path (cell00 G i j) (cell01 G i j) :=
  (Path.refl (G.coord i.castSucc)).prod (intervalPath (G.coord j.castSucc) (G.coord j.succ))
def topCoordEdge (i j : Fin G.N) : Path (cell10 G i j) (cell11 G i j) :=
  (Path.refl (G.coord i.succ)).prod (intervalPath (G.coord j.castSucc) (G.coord j.succ))
def leftCoordEdge (i j : Fin G.N) : Path (cell00 G i j) (cell10 G i j) :=
  (intervalPath (G.coord i.castSucc) (G.coord i.succ)).prod (Path.refl (G.coord j.castSucc))
def rightCoordEdge (i j : Fin G.N) : Path (cell01 G i j) (cell11 G i j) :=
  (intervalPath (G.coord i.castSucc) (G.coord i.succ)).prod (Path.refl (G.coord j.succ))

def bottomRightCoord (i j : Fin G.N) : Path (cell00 G i j) (cell11 G i j) :=
  (bottomCoordEdge G i j).trans (rightCoordEdge G i j)
def leftTopCoord (i j : Fin G.N) : Path (cell00 G i j) (cell11 G i j) :=
  (leftCoordEdge G i j).trans (topCoordEdge G i j)

theorem coordEdge_mem_cell (i j : Fin G.N) (t : unitInterval) :
    bottomRightCoord G i j t ∈ gridCell G.N G.N_pos i j ∧
      leftTopCoord G i j t ∈ gridCell G.N G.N_pos i j := by
  have hi : G.coord i.castSucc ≤ G.coord i.succ := by
    rw [G.coord_eq_grid]
    exact (monotone_gridCoord G.N G.N_pos) i.castSucc_le_succ
  have hj : G.coord j.castSucc ≤ G.coord j.succ := by
    rw [G.coord_eq_grid]
    exact (monotone_gridCoord G.N G.N_pos) j.castSucc_le_succ
  have hb (s : unitInterval) : bottomCoordEdge G i j s ∈ gridCell G.N G.N_pos i j := by
    change (G.coord i.castSucc, intervalLerp (G.coord j.castSucc) (G.coord j.succ) s) ∈ _
    change (gridCoord G.N G.N_pos i.castSucc ≤ G.coord i.castSucc ∧
      G.coord i.castSucc ≤ gridCoord G.N G.N_pos i.succ) ∧
      (gridCoord G.N G.N_pos j.castSucc ≤ intervalLerp (G.coord j.castSucc) (G.coord j.succ) s ∧
      intervalLerp (G.coord j.castSucc) (G.coord j.succ) s ≤ gridCoord G.N G.N_pos j.succ)
    rw [← G.coord_eq_grid]
    exact ⟨⟨le_rfl, hi⟩, intervalLerp_mem_Icc ⟨le_rfl, hj⟩ ⟨hj, le_rfl⟩⟩
  have hr (s : unitInterval) : rightCoordEdge G i j s ∈ gridCell G.N G.N_pos i j := by
    change (intervalLerp (G.coord i.castSucc) (G.coord i.succ) s, G.coord j.succ) ∈ _
    change (gridCoord G.N G.N_pos i.castSucc ≤ intervalLerp (G.coord i.castSucc) (G.coord i.succ) s ∧
      intervalLerp (G.coord i.castSucc) (G.coord i.succ) s ≤ gridCoord G.N G.N_pos i.succ) ∧
      (gridCoord G.N G.N_pos j.castSucc ≤ G.coord j.succ ∧
      G.coord j.succ ≤ gridCoord G.N G.N_pos j.succ)
    rw [← G.coord_eq_grid]
    exact ⟨intervalLerp_mem_Icc ⟨le_rfl, hi⟩ ⟨hi, le_rfl⟩, ⟨hj, le_rfl⟩⟩
  have hl (s : unitInterval) : leftCoordEdge G i j s ∈ gridCell G.N G.N_pos i j := by
    change (intervalLerp (G.coord i.castSucc) (G.coord i.succ) s, G.coord j.castSucc) ∈ _
    change (gridCoord G.N G.N_pos i.castSucc ≤ intervalLerp (G.coord i.castSucc) (G.coord i.succ) s ∧
      intervalLerp (G.coord i.castSucc) (G.coord i.succ) s ≤ gridCoord G.N G.N_pos i.succ) ∧
      (gridCoord G.N G.N_pos j.castSucc ≤ G.coord j.castSucc ∧
      G.coord j.castSucc ≤ gridCoord G.N G.N_pos j.succ)
    rw [← G.coord_eq_grid]
    exact ⟨intervalLerp_mem_Icc ⟨le_rfl, hi⟩ ⟨hi, le_rfl⟩, ⟨le_rfl, hj⟩⟩
  have ht (s : unitInterval) : topCoordEdge G i j s ∈ gridCell G.N G.N_pos i j := by
    change (G.coord i.succ, intervalLerp (G.coord j.castSucc) (G.coord j.succ) s) ∈ _
    change (gridCoord G.N G.N_pos i.castSucc ≤ G.coord i.succ ∧
      G.coord i.succ ≤ gridCoord G.N G.N_pos i.succ) ∧
      (gridCoord G.N G.N_pos j.castSucc ≤ intervalLerp (G.coord j.castSucc) (G.coord j.succ) s ∧
      intervalLerp (G.coord j.castSucc) (G.coord j.succ) s ≤ gridCoord G.N G.N_pos j.succ)
    rw [← G.coord_eq_grid]
    exact ⟨⟨hi, le_rfl⟩, intervalLerp_mem_Icc ⟨le_rfl, hj⟩ ⟨hj, le_rfl⟩⟩
  constructor
  · rw [bottomRightCoord, Path.trans_apply]
    split_ifs
    · exact hb _
    · exact hr _
  · rw [leftTopCoord, Path.trans_apply]
    split_ifs
    · exact hl _
    · exact ht _

/-- Pointwise convex interpolation between the two L-shaped coordinate paths. -/
def cellCoordHomotopy (i j : Fin G.N) :
    Path.Homotopy (bottomRightCoord G i j) (leftTopCoord G i j) where
  toFun z :=
    (intervalLerp (bottomRightCoord G i j z.2).1 (leftTopCoord G i j z.2).1 z.1,
      intervalLerp (bottomRightCoord G i j z.2).2 (leftTopCoord G i j z.2).2 z.1)
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk
    all_goals change Continuous fun z : unitInterval × unitInterval ↦
      (1 - (z.1 : ℝ)) * (_ : ℝ) + (z.1 : ℝ) * (_ : ℝ)
    all_goals fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' t s hs := by
    rcases hs with rfl | hs
    · apply Prod.ext <;> simp
    · rw [Set.mem_singleton_iff] at hs
      subst s
      apply Prod.ext <;> simp

theorem cellCoordHomotopy_mem (i j : Fin G.N) (z : unitInterval × unitInterval) :
    cellCoordHomotopy G i j z ∈ gridCell G.N G.N_pos i j := by
  rcases coordEdge_mem_cell G i j z.2 with ⟨hb, hl⟩
  exact ⟨intervalLerp_mem_Icc hb.1 hl.1, intervalLerp_mem_Icc hb.2 hl.2⟩

variable (H : Path.Homotopy p q)
  (G : HomotopySquareGrid H.toContinuousMap U V)

def cellPoint (i j : Fin G.N) (w : unitInterval × unitInterval)
    (hw : w ∈ gridCell G.N G.N_pos i j) : CoverPiece U V (G.side (i, j)) :=
  ⟨H w, G.cell_mem i j w hw⟩

theorem cell00_mem (i j : Fin G.N) : cell00 G i j ∈ gridCell G.N G.N_pos i j := by
  have hi := (monotone_gridCoord G.N G.N_pos) i.castSucc_le_succ
  have hj := (monotone_gridCoord G.N G.N_pos) j.castSucc_le_succ
  rw [cell00, G.coord_eq_grid]
  exact ⟨⟨le_rfl, hi⟩, ⟨le_rfl, hj⟩⟩

theorem cell11_mem (i j : Fin G.N) : cell11 G i j ∈ gridCell G.N G.N_pos i j := by
  have hi := (monotone_gridCoord G.N G.N_pos) i.castSucc_le_succ
  have hj := (monotone_gridCoord G.N G.N_pos) j.castSucc_le_succ
  rw [cell11, G.coord_eq_grid]
  exact ⟨⟨hi, le_rfl⟩, ⟨hj, le_rfl⟩⟩

/-- The bottom-right L path, lifted to the cell's selected cover piece. -/
def cellBottomRightPath (i j : Fin G.N) :
    Path (cellPoint H G i j (cell00 G i j) (cell00_mem H G i j))
      (cellPoint H G i j (cell11 G i j) (cell11_mem H G i j)) where
  toFun t := cellPoint H G i j (bottomRightCoord G i j t) (coordEdge_mem_cell G i j t).1
  continuous_toFun := by dsimp [cellPoint]; fun_prop
  source' := by
    apply Subtype.ext
    exact congrArg H (bottomRightCoord G i j).source
  target' := by
    apply Subtype.ext
    exact congrArg H (bottomRightCoord G i j).target

/-- The left-top L path, lifted to the same selected cover piece. -/
def cellLeftTopPath (i j : Fin G.N) :
    Path (cellPoint H G i j (cell00 G i j) (cell00_mem H G i j))
      (cellPoint H G i j (cell11 G i j) (cell11_mem H G i j)) where
  toFun t := cellPoint H G i j (leftTopCoord G i j t) (coordEdge_mem_cell G i j t).2
  continuous_toFun := by dsimp [cellPoint]; fun_prop
  source' := by
    apply Subtype.ext
    exact congrArg H (leftTopCoord G i j).source
  target' := by
    apply Subtype.ext
    exact congrArg H (leftTopCoord G i j).target

theorem cellBottomRightPath_eq_edges (i j : Fin G.N) :
    cellBottomRightPath H G i j =
      (cellBottomEdge H G i j).trans (cellRightEdge H G i j) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change H (bottomRightCoord G i j t) =
    (((cellBottomEdge H G i j).trans (cellRightEdge H G i j)) t).1
  rw [Path.trans_apply, bottomRightCoord, Path.trans_apply]
  split_ifs <;> rfl

theorem cellLeftTopPath_eq_edges (i j : Fin G.N) :
    cellLeftTopPath H G i j =
      (cellLeftEdge H G i j).trans (cellTopEdge H G i j) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change H (leftTopCoord G i j t) =
    (((cellLeftEdge H G i j).trans (cellTopEdge H G i j)) t).1
  rw [Path.trans_apply, leftTopCoord, Path.trans_apply]
  split_ifs <;> rfl

/-- The two L-shaped routes around a grid cell are homotopic relative to their
corners inside the cell's selected cover piece. -/
def cellBoundaryHomotopy (i j : Fin G.N) :
    Path.Homotopy (cellBottomRightPath H G i j) (cellLeftTopPath H G i j) where
  toFun z := cellPoint H G i j (cellCoordHomotopy G i j z)
    (cellCoordHomotopy_mem G i j z)
  continuous_toFun := by dsimp [cellPoint]; fun_prop
  map_zero_left s := by
    apply Subtype.ext
    exact congrArg H ((cellCoordHomotopy G i j).map_zero_left s)
  map_one_left s := by
    apply Subtype.ext
    exact congrArg H ((cellCoordHomotopy G i j).map_one_left s)
  prop' t s hs := by
    rcases hs with rfl | hs
    · apply Subtype.ext
      exact congrArg H ((cellCoordHomotopy G i j).source t |>.trans
        (bottomRightCoord G i j).source.symm)
    · rw [Set.mem_singleton_iff] at hs
      subst s
      apply Subtype.ext
      exact congrArg H ((cellCoordHomotopy G i j).target t |>.trans
        (bottomRightCoord G i j).target.symm)

/-- The relative homotopy in the requested four-edge presentation. -/
def cellEdgeBoundaryHomotopy (i j : Fin G.N) :
    Path.Homotopy
      ((cellBottomEdge H G i j).trans (cellRightEdge H G i j))
      ((cellLeftEdge H G i j).trans (cellTopEdge H G i j)) :=
  (cellBoundaryHomotopy H G i j).cast
    (cellBottomRightPath_eq_edges H G i j)
    (cellLeftTopPath_eq_edges H G i j)

theorem cellEdgeBoundary_quotient_eq (i j : Fin G.N) :
    Path.Homotopic.Quotient.mk
        ((cellBottomEdge H G i j).trans (cellRightEdge H G i j)) =
      Path.Homotopic.Quotient.mk
        ((cellLeftEdge H G i j).trans (cellTopEdge H G i j)) :=
  Quotient.sound ⟨cellEdgeBoundaryHomotopy H G i j⟩

theorem cellBoundary_quotient_eq (i j : Fin G.N) :
    Path.Homotopic.Quotient.mk (cellBottomRightPath H G i j) =
      Path.Homotopic.Quotient.mk (cellLeftTopPath H G i j) :=
  Quotient.sound ⟨cellBoundaryHomotopy H G i j⟩

universe v
variable {C : Type v} [CategoryTheory.Category C]

/-- Every descent datum's selected piece functor assigns the same morphism to
the two routes around a labelled cell. -/
theorem cellBoundary_piece_map_eq
    (D : @TwoOpenDescentDatum X _ U V C _ ) (i j : Fin G.N) :
    (D.functor (G.side (i, j))).map
        (Path.Homotopic.Quotient.mk (cellBottomRightPath H G i j)) =
      (D.functor (G.side (i, j))).map
        (Path.Homotopic.Quotient.mk (cellLeftTopPath H G i j)) := by
  exact congrArg (D.functor (G.side (i, j))).map
    (cellBoundary_quotient_eq H G i j)

theorem cellEdgeBoundary_piece_map_eq
    (D : @TwoOpenDescentDatum X _ U V C _ ) (i j : Fin G.N) :
    (D.functor (G.side (i, j))).map
        (Path.Homotopic.Quotient.mk
          ((cellBottomEdge H G i j).trans (cellRightEdge H G i j))) =
      (D.functor (G.side (i, j))).map
        (Path.Homotopic.Quotient.mk
          ((cellLeftEdge H G i j).trans (cellTopEdge H G i j))) :=
  congrArg (D.functor (G.side (i, j))).map
    (cellEdgeBoundary_quotient_eq H G i j)


#print axioms cellCoordHomotopy
#print axioms cellCoordHomotopy_mem
#print axioms cellBoundaryHomotopy
#print axioms cellBoundary_quotient_eq
#print axioms cellBoundary_piece_map_eq
#print axioms cellEdgeBoundaryHomotopy
#print axioms cellEdgeBoundary_quotient_eq
#print axioms cellEdgeBoundary_piece_map_eq

#print axioms verticalEdge
#print axioms verticalEdge_left_mem
#print axioms verticalEdge_right_mem
#print axioms cellBottomEdge
#print axioms cellTopEdge
#print axioms cellLeftEdge
#print axioms cellRightEdge

end ConstructionTargets.HomotopySquareCellBoundary
