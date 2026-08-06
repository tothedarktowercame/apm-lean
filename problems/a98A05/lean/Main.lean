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

theorem apm_a98a05 :
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ∂volume =
      2 * Real.pi / (3 * Real.sqrt 3) := by
  sorry
