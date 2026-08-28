import ConstructionTargets.HomotopySquareTwoOpenLebesgue

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.HomotopySquareUniformGrid

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.HomotopySquareTwoOpenLebesgue

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}

def gridCoord (N : ℕ) (hN : 0 < N) (i : Fin (N + 1)) : unitInterval :=
  ⟨(i : ℝ) / N, by
    constructor
    · positivity
    · rw [div_le_one (by positivity : (0 : ℝ) < N)]
      exact_mod_cast (Nat.le_of_lt_succ i.isLt)⟩

@[simp] theorem gridCoord_zero (N : ℕ) (hN : 0 < N) :
    gridCoord N hN 0 = 0 := by
  apply Subtype.ext
  simp [gridCoord]

@[simp] theorem gridCoord_last (N : ℕ) (hN : 0 < N) :
    gridCoord N hN (Fin.last N) = 1 := by
  apply Subtype.ext
  simp [gridCoord, Nat.ne_of_gt hN]

theorem strictMono_gridCoord (N : ℕ) (hN : 0 < N) :
    StrictMono (gridCoord N hN) := by
  intro i j hij
  apply Subtype.mk_lt_mk.mpr
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

theorem monotone_gridCoord (N : ℕ) (hN : 0 < N) :
    Monotone (gridCoord N hN) := (strictMono_gridCoord N hN).monotone

theorem dist_gridCoord_adjacent (N : ℕ) (hN : 0 < N) (i : Fin N) :
    dist (gridCoord N hN i.castSucc) (gridCoord N hN i.succ) = (1 : ℝ) / N := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [gridCoord, Subtype.coe_mk, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonpos]
  · ring
  · apply sub_nonpos.mpr
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)

def gridCell (N : ℕ) (hN : 0 < N) (i j : Fin N) :
    Set (unitInterval × unitInterval) :=
  Icc (gridCoord N hN i.castSucc) (gridCoord N hN i.succ) ×ˢ
    Icc (gridCoord N hN j.castSucc) (gridCoord N hN j.succ)

theorem gridCell_coordinatewise_close (N : ℕ) (hN : 0 < N)
    {δ : ℝ} (hmesh : (1 : ℝ) / N < δ) (i j : Fin N)
    (w : unitInterval × unitInterval) (hw : w ∈ gridCell N hN i j) :
    dist w.1 (gridCoord N hN i.castSucc) < δ ∧
      dist w.2 (gridCoord N hN j.castSucc) < δ := by
  rcases hw with ⟨hwi, hwj⟩
  have hwi0 : (gridCoord N hN i.castSucc : ℝ) ≤ (w.1 : ℝ) := hwi.1
  have hwi1 : (w.1 : ℝ) ≤ (gridCoord N hN i.succ : ℝ) := hwi.2
  have hwj0 : (gridCoord N hN j.castSucc : ℝ) ≤ (w.2 : ℝ) := hwj.1
  have hwj1 : (w.2 : ℝ) ≤ (gridCoord N hN j.succ : ℝ) := hwj.2
  constructor
  · change |(w.1 : ℝ) - (gridCoord N hN i.castSucc : ℝ)| < δ
    rw [abs_of_nonneg (show 0 ≤ (w.1 : ℝ) -
      (gridCoord N hN i.castSucc : ℝ) from sub_nonneg.mpr hwi0)]
    calc
      (w.1 : ℝ) - (gridCoord N hN i.castSucc : ℝ) ≤
          (gridCoord N hN i.succ : ℝ) - (gridCoord N hN i.castSucc : ℝ) :=
        sub_le_sub_right hwi1 _
      _ = (1 : ℝ) / N := by
        simp only [gridCoord, Subtype.coe_mk, Fin.val_succ, Fin.val_castSucc,
          Nat.cast_add, Nat.cast_one]
        ring
      _ < δ := hmesh
  · change |(w.2 : ℝ) - (gridCoord N hN j.castSucc : ℝ)| < δ
    rw [abs_of_nonneg (show 0 ≤ (w.2 : ℝ) -
      (gridCoord N hN j.castSucc : ℝ) from sub_nonneg.mpr hwj0)]
    calc
      (w.2 : ℝ) - (gridCoord N hN j.castSucc : ℝ) ≤
          (gridCoord N hN j.succ : ℝ) - (gridCoord N hN j.castSucc : ℝ) :=
        sub_le_sub_right hwj1 _
      _ = (1 : ℝ) / N := by
        simp only [gridCoord, Subtype.coe_mk, Fin.val_succ, Fin.val_castSucc,
          Nat.cast_add, Nat.cast_one]
        ring
      _ < δ := hmesh

/-- A uniform square grid subordinate to the pullback two-open cover.  The
first cell coordinate is homotopy time; the second is path parameter. -/
structure HomotopySquareGrid (F : C(unitInterval × unitInterval, X))
    (U V : Set X) where
  N : ℕ
  N_pos : 0 < N
  coord : Fin (N + 1) → unitInterval := gridCoord N N_pos
  coord_eq_grid : coord = gridCoord N N_pos
  radius : ℝ
  radius_pos : 0 < radius
  mesh_lt : (1 : ℝ) / N < radius
  side : Fin N × Fin N → Bool
  cell_mem : ∀ (i j : Fin N) (w : unitInterval × unitInterval),
    w ∈ gridCell N N_pos i j → F w ∈ twoChart U V (side (i, j))

/-- Construct a grid from a specific positive Lebesgue radius. -/
def HomotopySquareGrid.ofRadius
    (F : C(unitInterval × unitInterval, X))
    (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ∀ (A : Set (unitInterval × unitInterval))
      (z : unitInterval × unitInterval),
      (∀ w ∈ A, dist w.1 z.1 < δ ∧ dist w.2 z.2 < δ) →
      ∃ b : Bool, F '' A ⊆ twoChart U V b) :
    HomotopySquareGrid F U V := by
  let n := Classical.choose (exists_nat_one_div_lt hδ)
  have hn : 1 / ((n : ℝ) + 1) < δ :=
    Classical.choose_spec (exists_nat_one_div_lt hδ)
  let N := n + 1
  have hN : 0 < N := Nat.succ_pos n
  have hmesh : (1 : ℝ) / N < δ := by simpa [N] using hn
  let cellSide : Fin N × Fin N → Bool := fun ij ↦
    Classical.choose (hsmall (gridCell N hN ij.1 ij.2)
      (gridCoord N hN ij.1.castSucc, gridCoord N hN ij.2.castSucc)
      (gridCell_coordinatewise_close N hN hmesh ij.1 ij.2))
  refine
    { N := N
      N_pos := hN
      coord := gridCoord N hN
      coord_eq_grid := rfl
      radius := δ
      radius_pos := hδ
      mesh_lt := hmesh
      side := cellSide
      cell_mem := ?_ }
  intro i j w hw
  have hs := Classical.choose_spec (hsmall (gridCell N hN i j)
    (gridCoord N hN i.castSucc, gridCoord N hN j.castSucc)
    (gridCell_coordinatewise_close N hN hmesh i j))
  exact hs ⟨w, hw, rfl⟩

theorem exists_homotopySquareGrid
    (F : C(unitInterval × unitInterval, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Nonempty (HomotopySquareGrid F U V) := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_side_of_coordinatewise_small F hU hV hcover
  exact ⟨HomotopySquareGrid.ofRadius F δ hδ hsmall⟩

#print axioms strictMono_gridCoord
#print axioms dist_gridCoord_adjacent
#print axioms gridCell_coordinatewise_close
#print axioms HomotopySquareGrid.ofRadius
#print axioms exists_homotopySquareGrid

end ConstructionTargets.HomotopySquareUniformGrid
