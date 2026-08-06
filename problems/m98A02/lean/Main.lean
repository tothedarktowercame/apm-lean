import Mathlib

/-!
# APM m98A02 — bounded operators and the Neumann inverse

## Statement repairs

Part (b) forms `I-A`, so its operator must have equal domain and codomain.
The initial `A : X → Y` is therefore minimally specialized there to
`A : X → X`; part (a) remains stated for `X → Y`.
-/

theorem apm_m98a02 :
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (A : X →ₗ[ℝ] Y),
      (∃ C ≥ 0, ∀ x, ‖A x‖ ≤ C * ‖x‖) ↔ Continuous A) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y],
      Nonempty (CompleteSpace (X →L[ℝ] Y))) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (A : X →L[ℝ] X), ‖A‖ < 1 →
      ∃ B : X →L[ℝ] X,
        B.comp (ContinuousLinearMap.id ℝ X - A) = ContinuousLinearMap.id ℝ X ∧
        (ContinuousLinearMap.id ℝ X - A).comp B = ContinuousLinearMap.id ℝ X ∧
        1 / (1 + ‖A‖) ≤ ‖B‖ ∧ ‖B‖ ≤ 1 / (1 - ‖A‖)) := by
  sorry
