import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.CoveringDegree

/-! # t99J01: finite covers of a wedge of three circles

The base is an actual iterated point-wedge quotient. Covering degree requires
finite fibers, not just Nat.card (which returns zero for infinite types).
The first clause constructs a connected n-sheeted cover for every positive n.
The second classifies all connected n-sheeted covers. The source does not
require connected covers: the third clause therefore also records the group
at every point of every cover, using the sheet count of that path component.
No covering-space classification or Nielsen--Schreier theorem is assumed.
-/

open ConstructionTargets.StatementSurfaceModels ConstructionTargets.CoveringDegree

noncomputable section

/-- Sheets in the component containing e, measured over its image in the base. -/
def T99J01ComponentSheets {E : Type} [TopologicalSpace E]
    (p : E → ThreeCircles) (e : E) : ℕ :=
  Nat.card {x : E // p x = p e ∧ Joined e x}

theorem apm_t99j01 :
    (∀ n : ℕ, 0 < n → ∃ (E : Type) (_ : TopologicalSpace E)
      (p : E → ThreeCircles), PathConnectedSpace E ∧ IsKSheetedCover p n) ∧
    (∀ (E : Type) [TopologicalSpace E] [PathConnectedSpace E]
      (n : ℕ) (p : E → ThreeCircles), IsKSheetedCover p n →
      ∀ e : E, Nonempty (FundamentalGroup E e ≃* FreeGroup (Fin (2 * n + 1)))) ∧
    (∀ (E : Type) [TopologicalSpace E] (n : ℕ) (p : E → ThreeCircles),
      IsKSheetedCover p n → ∀ e : E,
      0 < T99J01ComponentSheets p e ∧ T99J01ComponentSheets p e ≤ n ∧
      Nonempty (FundamentalGroup E e ≃*
        FreeGroup (Fin (2 * T99J01ComponentSheets p e + 1)))) := by
  sorry
