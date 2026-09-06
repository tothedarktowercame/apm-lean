import Mathlib

noncomputable section

/-! The factors are reindexed by `n : ℕ`: factor `n` is the sphere
`S^(n+1)` of radius `n+1` in `ℝ^(n+2)`.  The function type carries the
product topology. -/

abbrev apm_t93j01_Factor (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) (n + 1 : ℝ)

abbrev apm_t93j01_Product := ∀ n : ℕ, apm_t93j01_Factor n

/-- Every continuous image of the indicated infinite product misses some
positive-radius sphere centred at the origin in `ℝ³`. -/
theorem apm_t93j01
    (f : ContinuousMap apm_t93j01_Product (EuclideanSpace ℝ (Fin 3))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, ‖f x‖ ≠ r := by
  sorry
