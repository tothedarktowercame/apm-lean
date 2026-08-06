import Mathlib

/-!
# APM m94A05

## Statement repairs

None.

## Encoding notes

Membership in `C([0,π])` is represented by a real function together with
`ContinuousOn` on the closed interval.  The explicit sufficient threshold
`ε < 1 / (4π)` is the contraction range from the standard sup-norm
argument.
-/

open Set
open scoped Interval

theorem apm_m94a05
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * Real.pi)) :
    ∃ u : ℝ → ℝ, ContinuousOn u (Icc 0 Real.pi) ∧
      ∀ t ∈ Icc (0 : ℝ) Real.pi,
        u t + ∫ s in (0 : ℝ)..Real.pi, Real.sin (t * s) * (u s) ^ 2 =
          ε * Real.sin t := by
  sorry
