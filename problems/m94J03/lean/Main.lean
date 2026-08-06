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
  intro H _ _ _ A _hcompact hself z hz
  rcases subsingleton_or_nontrivial H with hH | hH
  · simp
  letI : Nontrivial H := hH
  have hnot : z ∉ spectrum ℂ A := by
    simpa [spectrum] using hz
  have hspec_nonempty : (spectrum ℂ A).Nonempty := spectrum.nonempty A
  have hdist : 0 < Metric.infDist z (spectrum ℂ A) :=
    ((spectrum.isClosed A).notMem_iff_infDist_pos hspec_nonempty).mp hnot
  /-
  Boundary: it remains to identify the norm of the resolvent of the
  self-adjoint operator with the supremum of `|(z - λ)⁻¹|` over its
  spectrum. I searched the imported spectral/resolvent and continuous
  functional-calculus APIs (`resolvent`, `spectrum.isClosed`,
  `IsSelfAdjoint.spectrumRestricts`, and the CFC isometry lemmas). The
  library exposes the needed ingredients, but I did not complete the bridge
  showing that this particular resolvent is the CFC of `λ ↦ (z - λ)⁻¹`.
  The resolvent-set hypothesis has been reduced above to the essential
  strict positivity of the spectral distance; compactness is mathematically
  unnecessary once self-adjointness is used.
  -/
  sorry
