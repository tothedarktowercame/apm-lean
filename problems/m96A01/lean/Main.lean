import Mathlib

/-!
# APM m96A01 — nonzero eigenspaces of compact operators

## Statement repairs

None. Compactness is encoded by Mathlib's `IsCompactOperator`: bounded sets
have relatively compact image.
-/

theorem apm_m96a01 :
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
      (L : X →L[ℂ] X),
      IsCompactOperator L → ∀ (eigenvalue : ℂ), eigenvalue ≠ 0 →
        FiniteDimensional ℂ
          (LinearMap.ker (L.toLinearMap - eigenvalue • LinearMap.id)) := by
  sorry
