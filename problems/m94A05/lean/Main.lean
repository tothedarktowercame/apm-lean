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
open MeasureTheory
open scoped Interval

noncomputable def apm_m94a05_picard (ε : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ε * Real.sin t -
    ∫ s in (0 : ℝ)..Real.pi, Real.sin (t * s) * (u s) ^ 2

lemma apm_m94a05_picard_integrable
    {u : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 Real.pi)) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ Real.sin (t * s) * (u s) ^ 2)
      volume 0 Real.pi := by
  apply ContinuousOn.intervalIntegrable_of_Icc Real.pi_pos.le
  exact ((Real.continuous_sin.comp_continuousOn
    (continuous_const.mul continuous_id).continuousOn).mul (hu.pow 2))

/-- The pointwise estimate underlying invariance of the Picard ball. -/
lemma apm_m94a05_kernel_square_le
    (u : ℝ → ℝ) {R t s : ℝ} (hu : |u s| ≤ R) :
    |Real.sin (t * s) * (u s) ^ 2| ≤ R ^ 2 := by
  rw [abs_mul, abs_pow]
  apply (mul_le_of_le_one_left (sq_nonneg |u s|)
    (Real.abs_sin_le_one (t * s))).trans
  nlinarith [abs_nonneg (u s)]

/-- The pointwise polarization estimate used for contractivity. -/
lemma apm_m94a05_kernel_square_sub_le
    (u v : ℝ → ℝ) {R t s : ℝ}
    (hu : |u s| ≤ R) (hv : |v s| ≤ R) :
    |Real.sin (t * s) * ((u s) ^ 2 - (v s) ^ 2)| ≤
      (2 * R) * |u s - v s| := by
  rw [abs_mul]
  calc
    |Real.sin (t * s)| * |u s ^ 2 - v s ^ 2|
        ≤ |u s ^ 2 - v s ^ 2| :=
          mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)
    _ = |u s + v s| * |u s - v s| := by
      rw [sq_sub_sq, abs_mul]
    _ ≤ (2 * R) * |u s - v s| := by
      gcongr
      calc
        |u s + v s| ≤ |u s| + |v s| := abs_add_le _ _
        _ ≤ R + R := add_le_add hu hv
        _ = 2 * R := by ring

theorem apm_m94a05
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * Real.pi)) :
    ∃ u : ℝ → ℝ, ContinuousOn u (Icc 0 Real.pi) ∧
      ∀ t ∈ Icc (0 : ℝ) Real.pi,
        u t + ∫ s in (0 : ℝ)..Real.pi, Real.sin (t * s) * (u s) ^ 2 =
          ε * Real.sin t := by
  /-
  Boundary (closer hop 1): the raw Picard map is now defined as
  `apm_m94a05_picard`.  Its integral section is proved interval-integrable for
  every continuous input by `apm_m94a05_picard_integrable`.  The two scalar
  estimates needed for the sup-norm argument are compiled as
  `apm_m94a05_kernel_square_le` and
  `apm_m94a05_kernel_square_sub_le`; the latter uses the polarization identity
  and gives the uniform factor `2 * R` on a radius-`R` ball.

  The intended route uses the complete Banach space of continuous
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
  operator construction within the original pass.  Renewed searches of
  `LEMMA-INDEX.md`, `ConstructionTargets`, the continuous-map Hammerstein
  development in `m98A03`, the related convolution fixed-point development in
  `m99A06`, Mathlib's parametric-integral source, and git history found no
  packaged theorem completing this construction.  The remaining bridge is to
  prove continuity in `t`, bundle the Picard map on
  `ContinuousMap (Icc 0 π) ℝ`, lift the pointwise estimates to its sup norm,
  prove the radius-`2ε` ball invariant and contracting, and extract the fixed
  point as an unrestricted function.
  -/
  sorry
