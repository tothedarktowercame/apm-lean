# Proof outline — a97A06

Source: claude-1 batch 20260502 (sequence apm-daily-batch.md).

## Theorem statements (Lean)

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Real MeasureTheory Filter Topology Set

noncomputable section

/-- The auxiliary entire function F(z) = (e^{2iz} - 1 - 2iz)/z²,
    extended to the entire function with F(0) = -2. -/
def apm_a97A06_F (z : ℂ) : ℂ :=
  if z = 0 then -2
  else (Complex.exp (2 * I * z) - 1 - 2 * I * z) / z ^ 2

/-- F is entire (analytic on all of ℂ). -/
theorem apm_a97A06_F_analytic : AnalyticOn ℂ apm_a97A06_F univ := by sorry

/-- The integrand sin²(x)/x² (with value 1 at 0) is integrable on ℝ. -/
theorem apm_a97A06_integrable :
    IntegrableOn (fun x : ℝ => (Real.sin x) ^ 2 / x ^ 2) (Set.Ioi 0) volume := by sorry

/-- Real part identity: Re(F(x)) = -2 sin²(x)/x² for x ≠ 0. -/
theorem apm_a97A06_real_part
    (x : ℝ) (hx : x ≠ 0) :
    (apm_a97A06_F (x : ℂ)).re = -2 * (Real.sin x) ^ 2 / x ^ 2 := by sorry

/-- The semicircular arc integral of e^{2iz}/z² vanishes as R → ∞. -/
theorem apm_a97A06_arc_exp_vanishes :
    Tendsto (fun R : ℝ => ‖∫ θ in (0:ℝ)..π,
      (Complex.exp (2 * I * (R * Complex.exp (I * θ))) /
       (R * Complex.exp (I * θ)) ^ 2) * (I * R * Complex.exp (I * θ))‖)
      atTop (nhds 0) := by sorry

/-- The semicircular arc integral of 1/z² vanishes as R → ∞. -/
theorem apm_a97A06_arc_inv_sq_vanishes :
    Tendsto (fun R : ℝ => ‖∫ θ in (0:ℝ)..π,
      (1 / (R * Complex.exp (I * θ)) ^ 2) * (I * R * Complex.exp (I * θ))‖)
      atTop (nhds 0) := by sorry

/-- The arc integral of 1/z over the upper semicircle equals iπ. -/
theorem apm_a97A06_arc_inv_eq_iPi
    (R : ℝ) (hR : 0 < R) :
    ∫ θ in (0:ℝ)..π,
      (1 / (R * Complex.exp (I * θ))) * (I * R * Complex.exp (I * θ)) = I * π := by sorry

/-- Main result: ∫₀^∞ sin²(x)/x² dx = π/2. -/
theorem apm_a97A06_main :
    ∫ x in Set.Ioi (0:ℝ), (Real.sin x) ^ 2 / x ^ 2 = π / 2 := by sorry
```


## Mathlib cross-references

**Types/structures:**
- `ℂ` / `Complex`, `Complex.I` — complex numbers and imaginary unit
- `Complex.exp`, `Real.sin`, `Real.cos` — transcendentals
- `AnalyticOn`, `AnalyticAt` — analyticity (entireness)
- `MeasureTheory.IntegrableOn` — integrability on a set
- `intervalIntegral` (`∫ x in a..b, f x`) — interval integrals
- `MeasureTheory.integral` — Lebesgue integral
- `Set.Ioi`, `Set.Ico`, `Set.Icc` — intervals
- `circleIntegral` / `circleMap` — for the semicircular arc parameterization
- `Filter.atTop`, `Filter.Tendsto`, `nhds`

**Key lemmas:**
- `Complex.cos_two_mul` / `Real.cos_two_mul` — cos(2x) = 1 - 2sin²(x)
- `Complex.exp_eq_exp_re_mul_sin_add_cos` / `Complex.exp_mul_I` — Euler decomposition
- `Complex.exp_taylorSeries` / `analyticAt_exp` — exp is entire and given by power series
- `Complex.exp_sub_one_sub_id` (if exists) — Taylor remainder bounds
- `analyticOn_iff_eq_powerSeries_on_ball` / removable singularity lemma
- `Complex.differentiable_iff_analyticAt`
- `Complex.integral_circleMap` — circle integral via parameterization
- `intervalIntegral.integral_const`, `intervalIntegral.integral_one` — basic interval integrals
- `Complex.norm_exp` / `Complex.abs_exp` — |e^z| = e^{Re z}
- `Real.sin_nonneg_of_mem_Icc` — sin ≥ 0 on [0, π], for Jordan's lemma
- `intervalIntegral.norm_integral_le_of_norm_le_const` — ML estimate
- `Complex.contDiffOn.integral_eq` / `Complex.cauchyTheorem` for closed contour
- `MeasureTheory.integral_Iio_eq_integral_Ioi` / `integrable_of_even_function` — symmetry
- `Real.eulerMascheroni` (irrelevant here, but) `Real.tendsto_one_div_atTop_nhds_zero` — 1/R → 0
- `intervalIntegral.integral_comp_smul_deriv` / parameterization lemma
- `Complex.ofReal_div`, `Complex.ofReal_pow` — real-to-complex coercions

**Tactic hints:**
- `field_simp` — clear z², z denominators in Möbius-style algebra
- `ring` — verify Re(F) = -2 sin²(x)/x² algebraically after expanding e^{2ix}
- `simp [Complex.exp_mul_I, Complex.cos_two_mul]` — expand exponentials and trig
- `nlinarith` / `linarith` — close R > 0, π > 0, sin θ ≥ 0 inequalities
- `positivity` — for 0 < R, 0 < π, 0 ≤ sin θ on [0, π]
- `gcongr` — monotone manipulation of arc-integral bounds
- `apply Tendsto.const_mul` / `Tendsto.div_atTop` — limit composition
- `filter_upwards [eventually_gt_atTop 1] with R hR` — for R large enough
- `convert ... using 2` — match expressions up to small rewrites
- `refine ⟨?_, ?_⟩` — split conjunctions
- `exact?` — search for Cauchy's theorem / ML estimate / Jordan's lemma
- `norm_num [Real.pi_pos]` — π-arithmetic facts

## Blockers

- All theorem bodies are `sorry`. Codex cleanup pass to attempt closure.
- Mathlib lemma names above are conjectural — verify via `exact?` / `apply?`.
