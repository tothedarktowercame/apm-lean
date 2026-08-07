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
  /-
  Boundary: Mathlib's `ContinuousLinearMap.finite_dimensional_eigenspace`
  proves exactly this result under an additional ambient `CompleteSpace`
  hypothesis. Following its proof, I restricted `L` to the closed eigenspace
  using `IsCompactOperator.restrict`, rewrote the restriction as scalar
  multiplication with `Module.End.restrict_eigenspace`, and used
  `IsCompactOperator.smul_iff₀` to obtain compactness of the identity.

  The final generic Riesz step is blocked by the frozen omission of
  `CompleteSpace X`: `FiniteDimensional.of_isCompactOperator_id` and the
  packaged spectral theorem require completeness, while the lower-level
  `FiniteDimensional.of_isCompact_closedBall₀` requires assembling a
  `ContinuousSMul` instance on the eigenspace subtype compatible with the
  plain `LinearMap.ker` encoding. I also tried deriving compactness of the
  closed unit ball directly from
  `isCompactOperator_iff_isCompact_closure_image_closedBall`; the remaining
  subtype scalar-action/type-transport bridge did not close. Sibling
  `m01J03` uses the packaged theorem but has `CompleteSpace` and an inner
  product, so it does not discharge this frozen statement.
  -/
  sorry
