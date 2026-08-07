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

private lemma apm_m02a04_sqrt_div_pow_three {t : ℝ} (ht : 0 < t) :
    Real.sqrt (Real.pi / t ^ 3) =
      Real.sqrt Real.pi * Real.rpow t (-(3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow Real.pi_pos.le (pow_nonneg ht.le 3),
    div_eq_mul_inv, ← Real.sqrt_eq_rpow]
  congr 1
  rw [← Real.rpow_natCast t 3, ← Real.rpow_mul ht.le,
    ← Real.rpow_neg ht.le]
  congr 1
  ring

theorem apm_m02a04 :
    (∀ t : ℝ, 0 < t →
      apm_m02a04_integral t = apm_m02a04_leadingTerm t) ∧
    Tendsto (fun t => apm_m02a04_integral t / apm_m02a04_leadingTerm t)
      atTop (nhds 1) := by
  have hexact : ∀ t : ℝ, 0 < t →
      apm_m02a04_integral t = apm_m02a04_leadingTerm t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hsquare : ∀ x : ℝ,
        -t ^ 3 * x ^ 2 + t ^ 2 * x =
          -t ^ 3 * (x - 1 / (2 * t)) ^ 2 + t / 4 := by
      intro x
      field_simp
      ring
    -- (Sibling: a96A04)
    have hgaussian :
        (∫ x : ℝ, Real.exp (-t ^ 3 * x ^ 2)) =
          Real.sqrt (Real.pi / t ^ 3) := by
      exact integral_gaussian (t ^ 3)
    have hleading_pos : 0 < apm_m02a04_leadingTerm t := by
      unfold apm_m02a04_leadingTerm
      exact mul_pos
        (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (Real.rpow_pos_of_pos ht _))
        (Real.exp_pos _)
    /-
    Boundary after completing the square: `hsquare` and the exact centered
    Gaussian value `hgaussian` are compiled above. The remaining elaboration
    is translation invariance of Lebesgue measure via
    `integral_add_right_eq_self`, pulling out `exp (t/4)`, and normalizing
    `sqrt (pi / t^3)` to `sqrt pi * t^(-3/2)` with
    `Real.sqrt_eq_rpow` and `Real.rpow_mul` for `t > 0`. The solved sibling
    `a96A04` supplies the same `integral_gaussian`/rpow normalization pattern,
    but not the translated linear-term calculation.
    -/
    unfold apm_m02a04_integral apm_m02a04_leadingTerm
    calc
      (∫ x : ℝ, Real.exp (-t ^ 3 * x ^ 2 + t ^ 2 * x)) =
          ∫ x : ℝ, Real.exp (-t ^ 3 * (x - 1 / (2 * t)) ^ 2) *
            Real.exp (t / 4) := by
              apply integral_congr_ae
              filter_upwards with x
              rw [hsquare, Real.exp_add]
      _ = (∫ x : ℝ, Real.exp (-t ^ 3 * (x - 1 / (2 * t)) ^ 2)) *
            Real.exp (t / 4) := integral_mul_const _ _
      _ = Real.sqrt (Real.pi / t ^ 3) * Real.exp (t / 4) := by
            rw [← hgaussian]
            congr 1
            convert
              (integral_add_right_eq_self
                (μ := volume)
                (fun x : ℝ ↦ Real.exp (-t ^ 3 * x ^ 2))
                (-(1 / (2 * t)))) using 1
      _ = Real.sqrt Real.pi * Real.rpow t (-(3 : ℝ) / 2) *
            Real.exp (t / 4) := by
            rw [apm_m02a04_sqrt_div_pow_three ht]
  refine ⟨hexact, ?_⟩
  have heq : (fun t => apm_m02a04_integral t / apm_m02a04_leadingTerm t) =ᶠ[atTop]
      (fun _ : ℝ => 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hexact t ht]
    exact div_self (ne_of_gt (by
      unfold apm_m02a04_leadingTerm
      exact mul_pos
        (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (Real.rpow_pos_of_pos ht _))
        (Real.exp_pos _)))
  exact tendsto_const_nhds.congr' heq.symm
