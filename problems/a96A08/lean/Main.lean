/-
! # APM a96A08: Evaluate ∫_{-∞}^{∞} sin(πx)/(x²-x) dx

## Problem

Evaluate ∫_{-∞}^{∞} sin(πx)/(x²-x) dx.

## Answer: -2π

## Proof

The integrand sin(πx)/[x(x-1)] has removable singularities at x=0,1 (sin(πx)
vanishes at both) and decays as 1/x² at infinity, so it is absolutely integrable.

Partial fractions: 1/[x(x-1)] = 1/(x-1) - 1/x, so on [-R,R] (R>1):
  ∫ sin(πx)/[x(x-1)] = ∫ sin(πx)/(x-1) - ∫ sin(πx)/x.

The second integral: ∫_{-R}^R sin(πx)/x → π (scaled Dirichlet integral,
via ConstructionTargets.Sinc.tendsto_integral_sinc_pi_div_two).

The first integral: substituting u=x-1, sin(π(u+1))/u = -sin(πu)/u, giving
∫_{-R-1}^{R-1} (-sin(πu)/u) du. Since sin(πu)/u is even and both R-1, R+1 → ∞,
this tends to -π.

Total: -π - π = -2π.

## Dependencies

- `ConstructionTargets.Sinc.tendsto_integral_sinc_pi_div_two`
  (Memory: e-codexpilot-evaluate-the-Dirichlet-sinc-integral-by-Abel-regularization-and-uniform-tails)
- Partial-fraction decomposition 1/[x(x-1)] = 1/(x-1) - 1/x
  (Memory: e-j07-reuse-two-pole-partial-fraction-contour-pattern)
-/

import Mathlib
import ConstructionTargets.Sinc

open Real MeasureTheory intervalIntegral Filter Topology Set

noncomputable section

/-- sin(π(u+1)) = -sin(πu). -/
lemma sin_pi_shift (u : ℝ) :
    Real.sin (Real.pi * (u + 1)) = -Real.sin (Real.pi * u) := by
  rw [show Real.pi * (u + 1) = Real.pi * u + Real.pi from by ring,
      Real.sin_add]
  simp [Real.sin_pi, Real.cos_pi]

/-- sin(π(-x))/(-x) = sin(πx)/x (even). -/
lemma sin_pi_div_x_even (x : ℝ) :
    Real.sin (Real.pi * (-x)) / (-x) = Real.sin (Real.pi * x) / x := by
  rw [show Real.pi * (-x) = -(Real.pi * x) from by ring, Real.sin_neg]
  ring

/-- ∀ᵐ x ∂(volume.restrict s), x ≠ a  (since {a} has measure 0). -/
lemma ae_ne_restrict (s : Set ℝ) (a : ℝ) :
    ∀ᵐ x ∂(volume.restrict s), x ≠ a := by
  rw [ae_iff]
  have hsub : {x | ¬(x ≠ a)} ⊆ ({a} : Set ℝ) := by
    intro x hx; push_neg at hx; exact hx
  refine measure_mono_null hsub ?_
  rw [Measure.restrict_apply (measurableSet_singleton a)]
  have ha : volume ({a} : Set ℝ) = 0 := @Real.volume_singleton a
  have hsubset : ({a} : Set ℝ) ∩ s ⊆ ({a} : Set ℝ) := fun _ hx => hx.1
  have hle := (measure_mono hsubset).trans_eq ha
  exact le_bot_iff.mp hle

/-- sin(πx)/x is interval-integrable on any bounded interval. -/
lemma intervalIntegrable_sin_pi_div (a b : ℝ) :
    IntervalIntegrable (fun x => Real.sin (Real.pi * x) / x) volume a b := by
  apply IntervalIntegrable.congr_ae
    (f := fun x => Real.pi * Real.sinc (Real.pi * x))
    ((Real.continuous_sinc.comp
      (continuous_const.mul continuous_id)).intervalIntegrable a b
      |>.const_mul Real.pi)
  filter_upwards [ae_ne_restrict _ 0] with x hx
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
  field_simp

/-- sin(πx)/(x-1) is interval-integrable on any bounded interval. -/
lemma intervalIntegrable_sin_pi_div_sub_one (a b : ℝ) :
    IntervalIntegrable (fun x => Real.sin (Real.pi * x) / (x - 1)) volume a b := by
  have hcont : Continuous fun x => -(Real.pi * Real.sinc (Real.pi * (x - 1))) := by
    have : Continuous fun x => Real.pi * (x - 1) :=
      continuous_const.mul (continuous_id.sub continuous_const)
    exact (Real.continuous_sinc.comp this).const_mul Real.pi |>.neg
  apply IntervalIntegrable.congr_ae
    (f := fun x => -(Real.pi * Real.sinc (Real.pi * (x - 1))))
    (hcont.intervalIntegrable a b)
  filter_upwards [ae_ne_restrict _ 1] with x hx
  have hpi : Real.pi * (x - 1) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hx)
  rw [Real.sinc_of_ne_zero hpi]
  -- Goal: -(π * (sin(π*(x-1)) / (π*(x-1)))) = sin(πx) / (x-1)
  -- Use sin(πx) = -sin(π(x-1))
  have : Real.sin (Real.pi * x) = -Real.sin (Real.pi * (x - 1)) := by
    have := sin_pi_shift (x - 1)
    rw [show (x - 1) + 1 = x from by ring] at this
    exact this
  rw [this]
  field_simp

/-- Substitution: ∫_0^R sin(πx)/x dx = ∫_0^{πR} sin(t)/t dt. -/
lemma integral_sin_pi_div_subst (R : ℝ) :
    (∫ x in (0 : ℝ)..R, Real.sin (Real.pi * x) / x) =
      (∫ t in (0 : ℝ)..(Real.pi * R), Real.sin t / t) := by
  let f (t : ℝ) : ℝ := Real.sin t / t
  have hf : ∀ x, Real.sin (Real.pi * x) / x = Real.pi * f (x * Real.pi) := by
    intro x
    show Real.sin (Real.pi * x) / x = Real.pi * (Real.sin (x * Real.pi) / (x * Real.pi))
    rw [mul_comm x Real.pi]
    field_simp
  rw [show (∫ x in (0 : ℝ)..R, Real.sin (Real.pi * x) / x) =
        ∫ x in (0 : ℝ)..R, Real.pi * f (x * Real.pi) from
    intervalIntegral.integral_congr (g := fun x => Real.pi * f (x * Real.pi))
      (by intro x hx; exact hf x)]
  rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_right f Real.pi_ne_zero]
  simp [smul_eq_mul, zero_mul]
  rw [mul_comm R Real.pi]

/-- ∫_0^R sin(πx)/x dx → π/2.

(Memory: e-codexpilot-evaluate-the-Dirichlet-sinc-integral-by-Abel-regularization-and-uniform-tails)
-/
theorem tendsto_half_line_sin_pi_div :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sin (Real.pi * x) / x)
      atTop (nhds (Real.pi / 2)) := by
  have hsinc := ConstructionTargets.Sinc.tendsto_integral_sinc_pi_div_two
  have hpiR : Tendsto (fun R : ℝ => Real.pi * R) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos Real.pi_pos).mpr tendsto_id
  apply Tendsto.congr' ?_ (hsinc.comp hpiR)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [integral_sin_pi_div_subst R]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_ne_restrict _ 0] with x hx
  intro _
  exact (Real.sinc_of_ne_zero hx).symm

/-- Even-function integral: ∫_{-S₁}^0 f = ∫_0^{S₁} f when f is even. -/
lemma integral_even_neg_to_pos (S₁ : ℝ) (f : ℝ → ℝ) (heven : ∀ x, f (-x) = f x) :
    (∫ x in (-S₁)..(0 : ℝ), f x) = (∫ x in (0 : ℝ)..S₁, f x) := by
  rw [show (∫ x in (-S₁)..(0 : ℝ), f x) =
        (∫ x in (-S₁)..(0 : ℝ), (fun x => f (-x)) x) from
    intervalIntegral.integral_congr (g := fun x => f (-x))
      (by intro x hx; exact (heven x).symm)]
  rw [intervalIntegral.integral_comp_neg]
  congr 1 <;> ring

/-- For S₁, S₂ → +∞: ∫_{-S₁(R)}^{S₂(R)} sin(πx)/x dx → π. -/
theorem tendsto_gen_sin_pi_div
    (S₁ S₂ : ℝ → ℝ)
    (hS₁ : Tendsto S₁ atTop atTop)
    (hS₂ : Tendsto S₂ atTop atTop) :
    Tendsto (fun R : ℝ =>
      ∫ x in (-S₁ R)..(S₂ R), Real.sin (Real.pi * x) / x)
      atTop (nhds Real.pi) := by
  have hhalf := tendsto_half_line_sin_pi_div
  have hsplit : ∀ R, (∫ x in (-S₁ R)..(S₂ R),
      Real.sin (Real.pi * x) / x) =
      (∫ x in (-S₁ R)..(0 : ℝ), Real.sin (Real.pi * x) / x) +
      (∫ x in (0 : ℝ)..(S₂ R), Real.sin (Real.pi * x) / x) := by
    intro R
    rw [intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sin_pi_div _ _)
      (intervalIntegrable_sin_pi_div _ _)]
  have hneg : Tendsto (fun R => ∫ x in (-S₁ R)..(0 : ℝ),
      Real.sin (Real.pi * x) / x) atTop (nhds (Real.pi / 2)) := by
    rw [show (fun R => ∫ x in (-S₁ R)..(0 : ℝ),
      Real.sin (Real.pi * x) / x) = fun R =>
      ∫ x in (0 : ℝ)..(S₁ R), Real.sin (Real.pi * x) / x from
      by funext R; exact integral_even_neg_to_pos _ _ sin_pi_div_x_even]
    exact hhalf.comp hS₁
  have hpos : Tendsto (fun R => ∫ x in (0 : ℝ)..(S₂ R),
      Real.sin (Real.pi * x) / x) atTop (nhds (Real.pi / 2)) :=
    hhalf.comp hS₂
  apply Tendsto.congr' (by filter_upwards with R; exact hsplit R) ?_
  convert hneg.add hpos using 1 <;> ring

/-- Symmetric integral ∫_{-R}^R sin(πx)/x → π. -/
theorem tendsto_symm_sin_pi_div :
    Tendsto (fun R : ℝ => ∫ x in -R..R, Real.sin (Real.pi * x) / x)
      atTop (nhds Real.pi) :=
  tendsto_gen_sin_pi_div (fun R => R) (fun R => R) tendsto_id tendsto_id

/-- The integrand: sin(πx)/(x²-x). -/
def a96A08_f (x : ℝ) : ℝ :=
  Real.sin (Real.pi * x) / (x^2 - x)

/-- f = sin(πx)/(x-1) - sin(πx)/x on ℝ \ {0,1}. -/
lemma f_eq_pf (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    a96A08_f x = Real.sin (Real.pi * x) / (x - 1) - Real.sin (Real.pi * x) / x := by
  rw [a96A08_f]
  field_simp
  ring

/-- ∫_{-R}^R sin(πx)/(x-1) dx = -∫_{-R-1}^{R-1} sin(πu)/u du. -/
lemma integral_sin_pi_div_sub_one (R : ℝ) :
    (∫ x in -R..R, Real.sin (Real.pi * x) / (x - 1)) =
      -(∫ u in (-R - 1)..(R - 1), Real.sin (Real.pi * u) / u) := by
  have hcomp := intervalIntegral.integral_comp_add_right
    (f := fun u => Real.sin (Real.pi * (u + 1)) / u) (d := -1)
  have hcongr1 : (∫ x in -R..R,
      (fun u => Real.sin (Real.pi * (u + 1)) / u) (x + (-1))) =
      (∫ x in -R..R, Real.sin (Real.pi * x) / (x - 1)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    show Real.sin (Real.pi * (x + (-1) + 1)) / (x + (-1)) =
         Real.sin (Real.pi * x) / (x - 1)
    ring_nf
  rw [hcongr1, ← hcomp]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [sin_pi_shift]
  ring

/-- The symmetric improper integral of f → -2π. -/
theorem tendsto_symmetric_f :
    Tendsto (fun R : ℝ => ∫ x in -R..R, a96A08_f x)
      atTop (nhds (-(2 * Real.pi))) := by
  have hterm2 : Tendsto (fun R => ∫ x in -R..R,
      Real.sin (Real.pi * x) / x) atTop (nhds Real.pi) :=
    tendsto_symm_sin_pi_div
  have hterm1 : Tendsto (fun R =>
      -(∫ u in (-R - 1)..(R - 1), Real.sin (Real.pi * u) / u))
      atTop (nhds (-Real.pi)) := by
    have h := tendsto_gen_sin_pi_div (fun R => R + 1) (fun R => R - 1)
      (by simpa using tendsto_id.add tendsto_const_nhds)
      (by simpa using tendsto_id.add
        (tendsto_const_nhds : Tendsto (fun _ => (-1 : ℝ)) id atTop))
    exact h.neg
  apply Tendsto.congr' ?_ (hterm1.sub hterm2)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  have hf : (∫ x in -R..R, a96A08_f x) =
      (∫ x in -R..R,
        Real.sin (Real.pi * x) / (x - 1) - Real.sin (Real.pi * x) / x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_ne_restrict _ 0, ae_ne_restrict _ 1] with x hx0 hx1
    intro _
    exact f_eq_pf x hx0 hx1
  rw [hf, intervalIntegral.integral_sub
      (intervalIntegrable_sin_pi_div_sub_one _ _)
      (intervalIntegrable_sin_pi_div _ _),
      integral_sin_pi_div_sub_one]
  rfl

/-- a96A08_f is absolutely integrable on ℝ. -/
theorem a96A08_integrable : Integrable a96A08_f volume := by
  sorry

/-- **Main result**: ∫ sin(πx)/(x²-x) dvol = -2π. -/
theorem a96A08 : ∫ x, a96A08_f x ∂volume = -(2 * Real.pi) := by
  sorry

end
