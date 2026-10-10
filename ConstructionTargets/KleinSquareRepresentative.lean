import ConstructionTargets.KleinPlaneAffineAction

namespace KleinSquareRepresentative

open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupCoordinateNormalForm
open KleinPlaneAffineAction

theorem exists_halfOpenSquare_smul (p : ℝ × ℝ) :
    ∃ g : PresentedKleinGroup,
      0 ≤ (g • p).1 ∧ (g • p).1 < 1 ∧
      0 ≤ (g • p).2 ∧ (g • p).2 < 1 := by
  let n : ℤ := -⌊p.2⌋
  let s : ℝ := ((Multiplicative.toAdd
    (action (Multiplicative.ofAdd n) (Multiplicative.ofAdd 1)) : ℤ) : ℝ)
  let m : ℤ := -⌊s * p.1⌋
  let c : Coordinates := ⟨Multiplicative.ofAdd m, Multiplicative.ofAdd n⟩
  let g : PresentedKleinGroup := coordinateEquiv.symm c
  use g
  have hg : coordinateEquiv g = c := coordinateEquiv.apply_symm_apply c
  change 0 ≤ (coordinateAct (coordinateEquiv g) p).1 ∧
    (coordinateAct (coordinateEquiv g) p).1 < 1 ∧
    0 ≤ (coordinateAct (coordinateEquiv g) p).2 ∧
    (coordinateAct (coordinateEquiv g) p).2 < 1
  rw [hg]
  change 0 ≤ (m : ℝ) + s * p.1 ∧ (m : ℝ) + s * p.1 < 1 ∧
    0 ≤ (n : ℝ) + p.2 ∧ (n : ℝ) + p.2 < 1
  dsimp only [m, n]
  push_cast
  constructor
  · linarith [Int.floor_le (s * p.1)]
  constructor
  · linarith [Int.lt_floor_add_one (s * p.1)]
  constructor
  · linarith [Int.floor_le p.2]
  · linarith [Int.lt_floor_add_one p.2]

theorem exists_closedSquare_smul (p : ℝ × ℝ) :
    ∃ g : PresentedKleinGroup,
      0 ≤ (g • p).1 ∧ (g • p).1 ≤ 1 ∧
      0 ≤ (g • p).2 ∧ (g • p).2 ≤ 1 := by
  obtain ⟨g, hx0, hx1, hy0, hy1⟩ := exists_halfOpenSquare_smul p
  exact ⟨g, hx0, le_of_lt hx1, hy0, le_of_lt hy1⟩

#print axioms exists_halfOpenSquare_smul
#print axioms exists_closedSquare_smul

end KleinSquareRepresentative
