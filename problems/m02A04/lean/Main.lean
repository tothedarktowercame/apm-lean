import Mathlib

/-!
# APM m02A04 — large-parameter Gaussian integral

## Statement repairs

The printed exponent has `+t³x²`, for which the integral diverges when `t>0`.
Following the hint and intended asymptotic problem, the quadratic sign is
minimally corrected to `-t³x²`.
-/

open MeasureTheory Filter

noncomputable def apm_m02a04_integral (t : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-t ^ 3 * x ^ 2 + t ^ 2 * x)

noncomputable def apm_m02a04_leadingTerm (t : ℝ) : ℝ :=
  Real.sqrt Real.pi * Real.rpow t (-(3 : ℝ) / 2) * Real.exp (t / 4)

theorem apm_m02a04 :
    (∀ t : ℝ, 0 < t →
      apm_m02a04_integral t = apm_m02a04_leadingTerm t) ∧
    Tendsto (fun t => apm_m02a04_integral t / apm_m02a04_leadingTerm t)
      atTop (nhds 1) := by
  sorry
