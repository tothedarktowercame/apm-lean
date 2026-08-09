import Mathlib

/-!
# APM a99J10 — boundary uniqueness under square-root growth

## Statement repairs

The displayed bound `|f(x + iy)| ≤ |y|⁻¹ᐟ²` is singular when `y = 0`.
It is therefore imposed when `y ≠ 0`, which is the minimal domain restriction
needed to express the source's intended blow-up bound without assigning it a
spurious finite value on the real diameter.

## Encoding notes

The radial limit is expressed as `r → 1⁻` for every angle in `[0, 2π]`.
-/

open Set Filter MeasureTheory
open scoped Topology
open Metric

/-- Imaginary part of the standard radial parametrization. -/
lemma apm_a99J10_polar_im (r θ : ℝ) :
    (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im) =
      r * Real.sin θ := by
  simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]

/-- A radius in `[0,1)` parametrizes a point of the open unit disk. -/
lemma apm_a99J10_polar_mem_ball {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  rw [norm_mul, Complex.norm_exp]
  simpa [abs_of_nonneg hr0] using hr1

/-- The frozen growth hypothesis becomes an explicit angular majorant on
each circle. This is the input needed for a dominated boundary-limit route. -/
lemma apm_a99J10_polar_bound
    (f : ℂ → ℂ)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hsin : Real.sin θ ≠ 0) :
    ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
      Real.rpow |r * Real.sin θ| (-(1 : ℝ) / 2) := by
  have hb := hbound ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    (apm_a99J10_polar_mem_ball hr0.le hr1)
    (by rw [apm_a99J10_polar_im]; exact mul_ne_zero hr0.ne' hsin)
  simpa [apm_a99J10_polar_im] using hb

lemma apm_a99J10_integrable_rpow_neg_half :
    IntegrableOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
      (Ioo 0 (Real.pi / 2)) := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by positivity)]
  norm_num

lemma apm_a99J10_sin_rpow_le_first_quadrant
    {x : ℝ} (hx0 : 0 < x) (hxpi : x ≤ Real.pi / 2) :
    Real.rpow |Real.sin x| (-(1 : ℝ) / 2) ≤
      Real.rpow (2 / Real.pi * x) (-(1 : ℝ) / 2) := by
  have hlin : 0 < 2 / Real.pi * x := mul_pos (div_pos zero_lt_two Real.pi_pos) hx0
  have hsin : 2 / Real.pi * x ≤ |Real.sin x| :=
    (Real.mul_le_sin hx0.le hxpi).trans (le_abs_self _)
  exact Real.rpow_le_rpow_of_nonpos hlin hsin (by norm_num)

/-- For radii bounded below by `1/2`, the polar estimate has a single
radius-independent angular majorant.  This closes the uniform-domination
bookkeeping needed before applying dominated convergence. -/
lemma apm_a99J10_polar_bound_uniform
    (f : ℂ → ℂ)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    {r θ : ℝ} (hr : (1 : ℝ) / 2 ≤ r) (hr1 : r < 1)
    (hsin : Real.sin θ ≠ 0) :
    ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
      Real.rpow ((1 : ℝ) / 2) (-(1 : ℝ) / 2) *
        Real.rpow |Real.sin θ| (-(1 : ℝ) / 2) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  refine (apm_a99J10_polar_bound f hbound hr0 hr1 hsin).trans ?_
  rw [abs_mul, abs_of_pos hr0]
  change (r * |Real.sin θ|) ^ (-(1 : ℝ) / 2) ≤
    ((1 : ℝ) / 2) ^ (-(1 : ℝ) / 2) * |Real.sin θ| ^ (-(1 : ℝ) / 2)
  rw [Real.mul_rpow hr0.le (abs_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hr (by norm_num))
    (Real.rpow_nonneg (abs_nonneg _) _)

theorem apm_a99j10 (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    (hradial : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      Tendsto
        (fun r : ℝ => f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (𝓝[<] (1 : ℝ)) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  /-
  PARTIAL boundary (closer hop 3). This hop closes the radius-uniform
  domination step: `apm_a99J10_polar_bound_uniform` factors the negative power
  of `|r sin θ|` and, for `r ≥ 1/2`, bounds it by the fixed multiple

    `(1/2)⁻¹ᐟ² * |sin θ|⁻¹ᐟ²`.

  The earlier helpers already prove integrability of the model `x⁻¹ᐟ²` on the
  first quadrant and its Jordan-inequality domination of the sine singularity
  there. I searched interval-integral affine substitutions, sine periodicity,
  circle averages, Cauchy formulas, and dominated convergence again. No
  packaged lemma assembles the four translated/reflected quadrant estimates
  into integrability of `θ ↦ |sin θ|⁻¹ᐟ²` on `[0,2π]`, and no boundary-
  uniqueness theorem consumes the frozen pointwise radial limits directly.

  The remaining proof must therefore formalize those three symmetry
  transports, apply DCT to the parametrized Cauchy integrals for radii tending
  to one from below, and identify the same integrals with each interior value
  using the circle Cauchy formula.  Phragmén--Lindelöf still does not apply
  because its sector/strip theorems require continuous boundary control.

  HOP 4 (failed-with-statement). The affine interval-integrability API has
  translations and reflections, but applying it here still requires three
  explicit sine identities and four `IntegrableOn` union conversions. No
  existing theorem packages the result. The exact first missing lemma is:

      theorem apm_a99J10_integrableOn_abs_sin_rpow_neg_half :
          IntegrableOn
            (fun θ : ℝ => Real.rpow |Real.sin θ| (-(1 : ℝ) / 2))
            (Icc 0 (2 * Real.pi))

  After this lemma, the remaining analytic interface can be stated without
  hiding the domination hypothesis:

      theorem apm_a99J10_boundary_unique_of_angular_integrable
          (f : ℂ → ℂ)
          (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
          (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
            ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
          (hradial : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
            Tendsto
              (fun r : ℝ =>
                f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
              (𝓝[<] (1 : ℝ)) (𝓝 0))
          (hang : IntegrableOn
            (fun θ : ℝ => Real.rpow |Real.sin θ| (-(1 : ℝ) / 2))
            (Icc 0 (2 * Real.pi))) :
          ∀ z ∈ ball (0 : ℂ) 1, f z = 0

  The second statement is true by dominated convergence on circle Cauchy
  integrals, using `apm_a99J10_polar_bound_uniform`, followed by the Cauchy
  integral formula on each smaller circle. Proving it requires assembling the
  parametrized complex integrals and the one-sided radial filter; no searched
  declaration consumes these frozen pointwise radial limits directly.
  -/
  sorry
