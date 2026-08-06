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
  /-
  Boundary: the intended route uses the complete Banach space of continuous
  maps on the interval subtype and the closed sup-norm ball of radius `2 * ε`.
  One must construct the Picard map
  `u ↦ ε * sin - ∫ s, sin (t*s) * u(s)^2`, prove continuity in the
  parameter `t`, and establish the uniform estimates
  `‖T u‖ ≤ ε + π ‖u‖^2` and
  `‖T u - T v‖ ≤ π (‖u‖ + ‖v‖) ‖u-v‖`.

  I found the abstract fixed-point API `ContractingWith.fixedPoint` and the
  interval-integral norm estimates. Applying it here still requires packaging
  the nonlinear parameterized integral as a continuous map, proving the ball
  is invariant from `ε < 1 / (4 * π)`, defining the subtype self-map, and
  converting its fixed point back to the statement's unrestricted function
  with `ContinuousOn`. No compiled sibling supplied this full integral-
  operator construction within this pass.
  -/
  sorry
