import Mathlib

/-!
# APM a98A05

## Statement repairs

None.

## Encoding questions

None.  The improper integral over `(0, ∞)` is represented as the Lebesgue
integral over `Set.Ioi 0`.
-/

open MeasureTheory Set

/-- The real partial-fraction decomposition, with positivity facts packaged so
later improper-integration steps have no pole side conditions. -/
lemma apm_a98a05_partial_fractions {x : ℝ} (hx : 0 ≤ x) :
    0 < x + 1 ∧ 0 < x ^ 2 - x + 1 ∧
      1 / (1 + x ^ 3) =
        (1 / 3 : ℝ) / (x + 1) + (2 - x) / (3 * (x ^ 2 - x + 1)) := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
  refine ⟨hx1, hq, ?_⟩
  have hcubic : 1 + x ^ 3 = (x + 1) * (x ^ 2 - x + 1) := by ring
  rw [hcubic]
  let A : ℝ := x + 1
  let Q : ℝ := x ^ 2 - x + 1
  have hA : A ≠ 0 := by simpa [A] using ne_of_gt hx1
  have hQ : Q ≠ 0 := by simpa [Q] using ne_of_gt hq
  change 1 / (A * Q) = (1 / 3 : ℝ) / A + (2 - x) / (3 * Q)
  field_simp [hA, hQ]
  simp [A, Q]
  ring

theorem apm_a98a05 :
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ∂volume =
      2 * Real.pi / (3 * Real.sqrt 3) := by
  /-
  Boundary (closer hop 1): `apm_a98a05_partial_fractions` above now compiles
  the exact decomposition

  `1/(1+x³) = (1/3)/(x+1) + (2-x)/(3(x²-x+1))`

  on the nonnegative half-line and simultaneously proves both denominators
  positive.  Thus the remaining route is purely improper FTC with the
  antiderivative

  `(1/3) log (x+1) - (1/6) log (x²-x+1)
     + (1/√3) arctan ((2*x-1)/√3)`.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
  Gamma/Beta, improper-integral, substitution, logarithm, and arctangent
  sources, prior exact-integral artifacts, and git history found no packaged
  formula for `∫₀∞ 1/(1+x^n)` and no direct substitution reducing this
  integral to `betaIntegral (1/3) (2/3)`.  Mathlib does provide
  `integral_Ioi_of_hasDerivAt_of_tendsto'`, the derivative rules, and the
  Gamma reflection ingredients, but assembling either route still requires
  proving integrability and the cancellation of the two divergent logarithmic
  terms at infinity.  Closure should package the displayed antiderivative,
  prove its derivative using the compiled decomposition, and evaluate its
  limits at zero and infinity.
  -/
  sorry
