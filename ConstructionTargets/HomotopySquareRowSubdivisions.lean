import ConstructionTargets.HomotopySquareUniformGrid

/-!
# Horizontal rows of a subordinate homotopy grid
-/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.HomotopySquareRowSubdivisions

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.HomotopySquareUniformGrid

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}

/-- The horizontal path at one grid time. -/
def rowPath (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (r : Fin (G.N + 1)) :
    Path x y where
  toFun s := H (G.coord r, s)
  continuous_toFun := H.continuous.comp (by fun_prop)
  source' := H.source (G.coord r)
  target' := H.target (G.coord r)

@[simp] theorem rowPath_zero (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) :
    rowPath H G 0 = p := by
  apply Path.ext
  funext s
  change H (G.coord 0, s) = p s
  rw [G.coord_eq_grid, gridCoord_zero]
  exact H.map_zero_left s

@[simp] theorem rowPath_last (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) :
    rowPath H G (Fin.last G.N) = q := by
  apply Path.ext
  funext s
  change H (G.coord (Fin.last G.N), s) = q s
  rw [G.coord_eq_grid, gridCoord_last]
  exact H.map_one_left s

def rowSubdivisionN {F : C(unitInterval × unitInterval, X)}
    (G : HomotopySquareGrid F U V) : ℕ :=
  G.N - 1

theorem rowSubdivisionN_add_one
    {F : C(unitInterval × unitInterval, X)} (G : HomotopySquareGrid F U V) :
    rowSubdivisionN G + 1 = G.N := by
  unfold rowSubdivisionN
  have := G.N_pos
  omega

theorem rowSubdivisionN_add_two
    {F : C(unitInterval × unitInterval, X)} (G : HomotopySquareGrid F U V) :
    rowSubdivisionN G + 2 = G.N + 1 := by
  rw [show rowSubdivisionN G + 2 = (rowSubdivisionN G + 1) + 1 by omega,
    rowSubdivisionN_add_one]

def rowVertex {F : C(unitInterval × unitInterval, X)}
    (G : HomotopySquareGrid F U V)
    (j : Fin (rowSubdivisionN G + 2)) : unitInterval :=
  G.coord (Fin.cast (rowSubdivisionN_add_two G) j)

@[simp] theorem rowVertex_zero
    {F : C(unitInterval × unitInterval, X)} (G : HomotopySquareGrid F U V) :
    rowVertex G 0 = 0 := by
  rw [rowVertex, G.coord_eq_grid]
  exact gridCoord_zero G.N G.N_pos

@[simp] theorem rowVertex_last
    {F : C(unitInterval × unitInterval, X)} (G : HomotopySquareGrid F U V) :
    rowVertex G (Fin.last (rowSubdivisionN G + 1)) = 1 := by
  have hlast :
      Fin.cast (rowSubdivisionN_add_two G)
          (Fin.last (rowSubdivisionN G + 1)) = Fin.last G.N := by
    apply Fin.ext
    simp
  rw [rowVertex, hlast, G.coord_eq_grid, gridCoord_last]

theorem monotone_rowVertex
    {F : C(unitInterval × unitInterval, X)} (G : HomotopySquareGrid F U V) :
    Monotone (rowVertex G) := by
  intro i j hij
  rw [rowVertex, rowVertex, G.coord_eq_grid]
  exact monotone_gridCoord G.N G.N_pos (Fin.mk_le_mk.mpr hij)

def rowSegmentIndex {F : C(unitInterval × unitInterval, X)}
    (G : HomotopySquareGrid F U V)
    (j : Fin (rowSubdivisionN G + 1)) : Fin G.N :=
  Fin.cast (rowSubdivisionN_add_one G) j

/-- The bottom horizontal boundary of a grid strip, labelled by its cells. -/
def bottomSubdivision (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    PathTwoOpenSubdivision (rowPath H G i.castSucc) U V where
  n := rowSubdivisionN G
  vertex := rowVertex G
  side j := G.side (i, rowSegmentIndex G j)
  vertex_zero := rowVertex_zero G
  vertex_last := rowVertex_last G
  monotone_vertex := monotone_rowVertex G
  segment_mem := by
    intro j z hz
    apply G.cell_mem i (rowSegmentIndex G j)
      (G.coord i.castSucc, z)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [G.coord_eq_grid]
    · rw [G.coord_eq_grid]
      exact (monotone_gridCoord G.N G.N_pos) i.castSucc_le_succ
    · simpa [rowVertex, rowSegmentIndex, G.coord_eq_grid] using hz

/-- The top horizontal boundary of a grid strip, with the same cell labels as
its bottom boundary. -/
def topSubdivision (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    PathTwoOpenSubdivision (rowPath H G i.succ) U V where
  n := rowSubdivisionN G
  vertex := rowVertex G
  side j := G.side (i, rowSegmentIndex G j)
  vertex_zero := rowVertex_zero G
  vertex_last := rowVertex_last G
  monotone_vertex := monotone_rowVertex G
  segment_mem := by
    intro j z hz
    apply G.cell_mem i (rowSegmentIndex G j)
      (G.coord i.succ, z)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [G.coord_eq_grid]
      exact (monotone_gridCoord G.N G.N_pos) i.castSucc_le_succ
    · rw [G.coord_eq_grid]
    · simpa [rowVertex, rowSegmentIndex, G.coord_eq_grid] using hz

@[simp] theorem bottomSubdivision_vertex (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    (bottomSubdivision H G i).vertex = rowVertex G := rfl

@[simp] theorem topSubdivision_vertex (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    (topSubdivision H G i).vertex = rowVertex G := rfl

@[simp] theorem bottomSubdivision_side (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N)
    (j : Fin (rowSubdivisionN G + 1)) :
    (bottomSubdivision H G i).side j = G.side (i, rowSegmentIndex G j) := rfl

@[simp] theorem topSubdivision_side (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N)
    (j : Fin (rowSubdivisionN G + 1)) :
    (topSubdivision H G i).side j = G.side (i, rowSegmentIndex G j) := rfl

#print axioms rowPath
#print axioms rowPath_zero
#print axioms rowPath_last
#print axioms bottomSubdivision
#print axioms topSubdivision

end ConstructionTargets.HomotopySquareRowSubdivisions
