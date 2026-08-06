import Mathlib

/-!
# APM m94J03

## Statement repairs

The resolvent `(z-A)⁻¹` exists only for `z` outside the spectrum, so the
printed quantifier "for all `z ∈ ℂ`" is minimally restricted to the
resolvent set. No value is assigned to a nonexistent inverse on the spectrum.

## Encoding questions

Mathlib's `resolvent A z` is the inverse of `z•1 - A` in the Banach algebra of
bounded operators. Distance to the spectrum is `Metric.infDist`.
-/

theorem apm_m94j03 :
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A →
      IsSelfAdjoint A →
      ∀ z ∈ resolventSet ℂ A,
        ‖resolvent A z‖ ≤ (Metric.infDist z (spectrum ℂ A))⁻¹ := by
  sorry
