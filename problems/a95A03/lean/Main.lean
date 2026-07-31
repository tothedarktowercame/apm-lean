/-
! # APM a95A03: Lp membership, integral, and convolution for |x|⁻²(1+|x|²)⁻¹ in ℝ³

This file formalizes three parts:
(a) For which p is f(x) = ‖x‖⁻²(1+‖x‖²)⁻¹ in L^p(ℝ³)?
(b) Compute ∫_{ℝ³} f dm₃.
(c) Show f * g ∈ L²(ℝ³) for g ∈ L² and find an explicit constant.

## Statement repair

The auto-generated statements used `Fin 3 → ℝ` for ℝ³. We repair to
`EuclideanSpace ℝ (Fin 3)` because:
- It carries the correct inner product structure so `‖x‖` is the Euclidean norm.
- Mathlib's volume lemmas (e.g., `volume_ball_fin_three`) are stated for
  `EuclideanSpace ℝ (Fin 3)`.
- The Japanese bracket integrability lemmas work on this type.

The generated `f_radial` used `‖x‖⁻²` which requires `‖x‖ ≠ 0` (i.e., `x ≠ 0`).
We define `f_radial` using an if-then-else: f(0) = 0 (value at a null point
is irrelevant for integration).

## Theory boundaries

1. Spherical coordinate reduction for radial integrals in R^3 (parts a, b),
   supplied by `ConstructionTargets.RadialIntegrationR3` over Mathlib's
   additive-Haar polar formula.
2. Young's convolution inequality for Lp norms (part c), proved here in the
   required `L¹ * L²` specialization by weighted Cauchy--Schwarz and Tonelli.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import ConstructionTargets.RadialIntegrationR3
import YoungL2

open MeasureTheory Set Module Real
open scoped ENNReal NNReal

noncomputable section

/-- The ambient space R^3. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The function f(x) = |x|^{-2} (1+|x|^2)^{-1} on R^3.

This function has a singularity at the origin. We define it pointwise:
at x = 0, |x| = 0 so |x|^{-2} is undefined. We set f(0) = 0 (the value at a
single point is irrelevant for integration since {0} has Lebesgue measure 0). -/
def f_radial (x : E) : ℝ :=
  if x = 0 then 0 else ‖x‖⁻¹ ^ 2 * (1 + ‖x‖ ^ 2)⁻¹

/-- Part (b) building block: the key 1D integral.

  integral from 0 to infinity of 1/(1+r^2) dr = pi/2.

This is directly from Mathlib's `integral_Ioi_inv_one_add_sq`. -/
lemma integral_inv_one_plus_sq :
    ∫ r in Ioi (0:ℝ), (1 + r ^ 2)⁻¹ ∂volume = π / 2 := by
  rw [integral_Ioi_inv_one_add_sq, arctan_zero]
  ring

/-- The full integral over R: integral of 1/(1+x^2) dx = pi. -/
lemma integral_univ_inv_one_plus_sq_eq :
    ∫ (x : ℝ), (1 + x ^ 2)⁻¹ ∂volume = π :=
  integral_univ_inv_one_add_sq

/-- finrank of R over E = 3. Needed for Japanese bracket lemmas. -/
lemma finrank_E_eq_three :
    finrank ℝ E = 3 := by
  simp [E]

/-- Part (b): integral of f over R^3 = 2 * pi^2.

**Informal computation.** Switching to spherical coordinates:
  integral f = 4*pi * integral_0^inf  r^2 / (r^2 (1+r^2)) dr
             = 4*pi * integral_0^inf  1/(1+r^2) dr
             = 4*pi * (pi/2) = 2*pi^2.

**Blocker:** The spherical coordinate reduction formula
  integral_{R^3} g(|x|) dx = 4*pi * integral_0^inf g(r) r^2 dr
is not available in Mathlib for n = 3.

What was tried:
- Search for polar/spherical coordinate integration lemmas in Mathlib.
- `integrable_rpow_neg_one_add_norm_sq` handles integrability but not
  explicit evaluation of integrals of radial functions.
- The `EuclideanSpace` volume lemmas give ball volumes (4*pi/3 * r^3)
  but not a general radial integral reduction formula.
- A genuine proof would need either:
  (a) A polar coordinates theorem (not in Mathlib), or
  (b) Direct Fubini computation over 3 coordinates (extremely tedious).

The 1D building block `integral_inv_one_plus_sq` IS proved above. -/
theorem f_radial_integral :
    ∫ x : E, f_radial x ∂volume = 2 * π ^ 2 := by
  let profile : ℝ → ℝ := fun r =>
    if r = 0 then 0 else r⁻¹ ^ 2 * (1 + r ^ 2)⁻¹
  have hradial : f_radial = fun x : E => profile ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · simp [f_radial, profile, hx]
    · simp [f_radial, profile, hx, norm_ne_zero_iff.mpr hx]
  have hint : Integrable (fun x : E => profile ‖x‖) volume := by
    rw [ConstructionTargets.RadialIntegrationR3.integrable_radial_R3_iff]
    refine integrable_inv_one_add_sq.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp only [profile, if_neg hr0]
    field_simp
  rw [hradial,
    ConstructionTargets.RadialIntegrationR3.radial_integral_R3 hint]
  have hprofile :
      (∫ r in Ioi (0 : ℝ), profile r * r ^ 2 ∂volume) = π / 2 := by
    rw [← integral_inv_one_plus_sq]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp only [profile, if_neg hr0]
    field_simp
  rw [hprofile]
  ring

/-- Part (a): f is in L^p(R^3) if and only if 3/4 < p < 3/2.

**Informal argument.** In spherical coordinates:
  integral |f|^p = 4*pi * integral_0^inf r^{2-2p} (1+r^2)^{-p} dr.
- Near r = 0: integrand ~ r^{2-2p}, integrable iff 2-2p > -1, i.e. p < 3/2.
- Near r = inf: integrand ~ r^{2-4p}, integrable iff 2-4p < -1, i.e. p > 3/4.

**Blocker:** Requires spherical coordinate reduction + power-law integrability
at singularities. The combination is not in Mathlib.

What was tried:
- `integrable_rpow_neg_one_add_norm_sq` handles the decay at infinity
  (Japanese bracket part) when the exponent is large enough.
- The singularity at 0 (the |x|^{-2} factor) needs separate treatment.
- Mathlib's `integrable_rpow_Ioi` type lemmas handle 1D power-law
  integrability, but connecting them to the 3D integral via polar
  coordinates is the missing piece. -/
theorem f_radial_memLp_iff {p : ℝ} (hp : 0 < p) :
    MemLp f_radial (ENNReal.ofReal p) (volume : Measure E) ↔
      3/4 < p ∧ p < 3/2 := by
  let profile : ℝ → ℝ := fun r =>
    if r = 0 then 0 else r⁻¹ ^ 2 * (1 + r ^ 2)⁻¹
  have hradial : f_radial = fun x : E => profile ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · simp [f_radial, profile, hx]
    · simp [f_radial, profile, hx, norm_ne_zero_iff.mpr hx]
  have hprofile_meas : Measurable profile := by
    dsimp only [profile]
    refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
    fun_prop
  have hmeas :
      AEStronglyMeasurable (fun x : E => profile ‖x‖) volume :=
    (hprofile_meas.comp continuous_norm.measurable).aestronglyMeasurable
  rw [hradial,
    ConstructionTargets.RadialIntegrationR3.memLp_radial_R3_iff hmeas
      (ENNReal.ofReal_pos.mpr hp).ne' (by simp)]
  rw [ENNReal.toReal_ofReal hp.le]
  have hformula (r : ℝ) (hr : 0 < r) :
      r ^ 2 * ‖profile r‖ ^ p =
        r ^ (2 - 2 * p) * (1 + r ^ 2) ^ (-p) := by
    have hr0 : r ≠ 0 := hr.ne'
    have hden : 0 < 1 + r ^ 2 := by positivity
    simp only [profile, if_neg hr0, Real.norm_eq_abs,
      abs_of_pos (mul_pos (sq_pos_of_pos (inv_pos.mpr hr))
        (inv_pos.mpr hden))]
    rw [Real.mul_rpow (sq_nonneg _) (inv_nonneg.mpr hden.le),
      Real.inv_rpow hden.le,
      ← Real.rpow_neg hden.le,
      ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul,
      Real.inv_rpow hr.le,
      ← Real.rpow_neg hr.le,
      ← mul_assoc,
      ← Real.rpow_add hr]
    congr 2
    all_goals positivity
  let radialDensity : ℝ → ℝ := fun r =>
    r ^ (2 - 2 * p) * (1 + r ^ 2) ^ (-p)
  have hdensity_congr :
      IntegrableOn (fun r : ℝ => r ^ 2 * ‖profile r‖ ^ p) (Ioi 0) ↔
        IntegrableOn radialDensity (Ioi 0) := by
    apply integrableOn_congr_fun
    · intro r hr
      exact hformula r hr
    · exact measurableSet_Ioi
  rw [hdensity_congr]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    integrableOn_union, integrableOn_Ioc_iff_integrableOn_Ioo]
  let nearPower : ℝ → ℝ := fun r => r ^ (2 - 2 * p)
  let farPower : ℝ → ℝ := fun r => r ^ (2 - 4 * p)
  have hnear_bounds (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      2 ^ (-p) ≤ (1 + r ^ 2) ^ (-p) ∧
        (1 + r ^ 2) ^ (-p) ≤ 1 := by
    have hb0 : 0 < 1 + r ^ 2 := by positivity
    have hb1 : 1 ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg r]
    have hb2 : 1 + r ^ 2 ≤ 2 := by
      nlinarith [mul_nonneg hr.1.le (sub_nonneg.mpr hr.2.le)]
    exact ⟨Real.rpow_le_rpow_of_nonpos hb0 hb2 (by linarith),
      Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith)⟩
  have hnear :
      IntegrableOn radialDensity (Ioo (0 : ℝ) 1) ↔
        IntegrableOn nearPower (Ioo (0 : ℝ) 1) := by
    have hnear_meas :
        AEStronglyMeasurable nearPower (volume.restrict (Ioo (0 : ℝ) 1)) := by
      dsimp only [nearPower]
      fun_prop
    have hdensity_meas :
        AEStronglyMeasurable radialDensity (volume.restrict (Ioo (0 : ℝ) 1)) := by
      dsimp only [radialDensity]
      fun_prop
    constructor
    · intro hD
      refine (hD.const_mul (2 ^ p)).mono' hnear_meas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hP0 : 0 ≤ nearPower r := Real.rpow_nonneg hr.1.le _
      have hD0 : 0 ≤ radialDensity r := mul_nonneg (Real.rpow_nonneg hr.1.le _)
        (Real.rpow_nonneg (by positivity) _)
      have hC0 : 0 ≤ (2 : ℝ) ^ p :=
        Real.rpow_nonneg (by norm_num) _
      have hone : 1 ≤ (2 : ℝ) ^ p * (1 + r ^ 2) ^ (-p) := by
        calc
          1 = (2 : ℝ) ^ p * 2 ^ (-p) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            norm_num
          _ ≤ (2 : ℝ) ^ p * (1 + r ^ 2) ^ (-p) :=
            mul_le_mul_of_nonneg_left (hnear_bounds r hr).1 hC0
      have hdom : nearPower r ≤ (2 : ℝ) ^ p * radialDensity r := by
        calc
          nearPower r = nearPower r * 1 := by ring
          _ ≤ nearPower r * ((2 : ℝ) ^ p * (1 + r ^ 2) ^ (-p)) :=
            mul_le_mul_of_nonneg_left hone hP0
          _ = (2 : ℝ) ^ p * radialDensity r := by
            simp only [nearPower, radialDensity]
            ring
      simpa only [Real.norm_eq_abs, abs_of_nonneg hP0,
        abs_of_nonneg (mul_nonneg hC0 hD0)] using hdom
    · intro hP
      refine hP.mono' hdensity_meas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hP0 : 0 ≤ nearPower r := Real.rpow_nonneg hr.1.le _
      have hD0 : 0 ≤ radialDensity r := mul_nonneg (Real.rpow_nonneg hr.1.le _)
        (Real.rpow_nonneg (by positivity) _)
      have hdom : radialDensity r ≤ nearPower r := by
        dsimp only [radialDensity, nearPower]
        exact mul_le_of_le_one_right (Real.rpow_nonneg hr.1.le _)
          (hnear_bounds r hr).2
      simpa only [Real.norm_eq_abs, abs_of_nonneg hD0,
        abs_of_nonneg hP0] using hdom
  rw [hnear,
    intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1)]
  have hfar_formula (r : ℝ) (hr : 0 < r) :
      radialDensity r = farPower r * (1 + r⁻¹ ^ 2) ^ (-p) := by
    have hr0 : r ≠ 0 := hr.ne'
    have hbase : 1 + r ^ 2 = r ^ 2 * (1 + r⁻¹ ^ 2) := by
      field_simp
      ring
    have hrpow_sq : (r ^ 2) ^ (-p) = r ^ (-2 * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      · congr 1
        ring
      · exact hr.le
    dsimp only [radialDensity, farPower]
    rw [hbase, Real.mul_rpow (sq_nonneg r) (by positivity), hrpow_sq,
      ← mul_assoc, ← Real.rpow_add hr]
    congr 2
    ring
  have hfar_bounds (r : ℝ) (hr : r ∈ Ioi (1 : ℝ)) :
      2 ^ (-p) ≤ (1 + r⁻¹ ^ 2) ^ (-p) ∧
        (1 + r⁻¹ ^ 2) ^ (-p) ≤ 1 := by
    apply hnear_bounds r⁻¹
    exact ⟨inv_pos.mpr (zero_lt_one.trans hr),
      (inv_lt_one₀ (zero_lt_one.trans hr)).mpr hr⟩
  have hfar :
      IntegrableOn radialDensity (Ioi (1 : ℝ)) ↔
        IntegrableOn farPower (Ioi (1 : ℝ)) := by
    have hfar_meas :
        AEStronglyMeasurable farPower (volume.restrict (Ioi (1 : ℝ))) := by
      dsimp only [farPower]
      fun_prop
    have hdensity_meas :
        AEStronglyMeasurable radialDensity (volume.restrict (Ioi (1 : ℝ))) := by
      dsimp only [radialDensity]
      fun_prop
    constructor
    · intro hD
      refine (hD.const_mul (2 ^ p)).mono' hfar_meas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := zero_lt_one.trans hr
      have hP0 : 0 ≤ farPower r := Real.rpow_nonneg hr0.le _
      have hD0 : 0 ≤ radialDensity r := mul_nonneg (Real.rpow_nonneg hr0.le _)
        (Real.rpow_nonneg (by positivity) _)
      have hC0 : 0 ≤ (2 : ℝ) ^ p :=
        Real.rpow_nonneg (by norm_num) _
      have hone : 1 ≤ (2 : ℝ) ^ p * (1 + r⁻¹ ^ 2) ^ (-p) := by
        calc
          1 = (2 : ℝ) ^ p * 2 ^ (-p) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            norm_num
          _ ≤ (2 : ℝ) ^ p * (1 + r⁻¹ ^ 2) ^ (-p) :=
            mul_le_mul_of_nonneg_left (hfar_bounds r hr).1 hC0
      have hdom : farPower r ≤ (2 : ℝ) ^ p * radialDensity r := by
        calc
          farPower r = farPower r * 1 := by ring
          _ ≤ farPower r * ((2 : ℝ) ^ p * (1 + r⁻¹ ^ 2) ^ (-p)) :=
            mul_le_mul_of_nonneg_left hone hP0
          _ = (2 : ℝ) ^ p * radialDensity r := by
            rw [hfar_formula r hr0]
            ring
      simpa only [Real.norm_eq_abs, abs_of_nonneg hP0,
        abs_of_nonneg (mul_nonneg hC0 hD0)] using hdom
    · intro hP
      refine hP.mono' hdensity_meas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := zero_lt_one.trans hr
      have hP0 : 0 ≤ farPower r := Real.rpow_nonneg hr0.le _
      have hD0 : 0 ≤ radialDensity r := mul_nonneg (Real.rpow_nonneg hr0.le _)
        (Real.rpow_nonneg (by positivity) _)
      have hdom : radialDensity r ≤ farPower r := by
        rw [hfar_formula r hr0]
        exact mul_le_of_le_one_right hP0 (hfar_bounds r hr).2
      simpa only [Real.norm_eq_abs, abs_of_nonneg hD0,
        abs_of_nonneg hP0] using hdom
  rw [hfar, integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
  constructor <;> rintro ⟨hnear', hfar'⟩ <;> constructor <;> linarith

/-- Part (a): f is not in L^infinity(R^3).

The function has a singularity at 0: lim_{x to 0} f(x) = infinity since
|x|^{-2} tends to infinity. So ess sup |f| = infinity. -/
theorem f_radial_not_memLp_top :
    ¬ MemLp f_radial ⊤ (volume : Measure E) := by
  intro hf
  have hess : eLpNormEssSup f_radial volume < ⊤ := by
    simpa only [eLpNorm_exponent_top] using hf.eLpNorm_lt_top
  rcases eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hess with ⟨C, hC⟩
  let δ : ℝ := (4 * ((C : ℝ) + 1))⁻¹
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    apply (inv_lt_one₀ (by positivity)).2
    have hC0 : 0 ≤ (C : ℝ) := C.coe_nonneg
    nlinarith
  have hne : ∀ᵐ x : E ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := volume) (0 : E))
  have hout : ∀ᵐ x : E ∂volume, x ∉ Metric.ball 0 δ := by
    filter_upwards [hC, hne] with x hxC hx0
    intro hxball
    have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hrδ : ‖x‖ < δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxball
    have hr1 : ‖x‖ < 1 := hrδ.trans hδ_lt_one
    have hdenom_pos : 0 < ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) := by positivity
    have hdenom_lt : ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) <
        1 / ((C : ℝ) + 1) := by
      have hC0 : 0 ≤ (C : ℝ) := C.coe_nonneg
      have hC1 : 0 < (C : ℝ) + 1 := by positivity
      have hr_sq_lt : ‖x‖ ^ 2 < ‖x‖ := by nlinarith [sq_nonneg (‖x‖)]
      have hdenom_lt_two_r : ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) < 2 * ‖x‖ := by
        nlinarith [sq_nonneg (‖x‖), sq_nonneg (‖x‖ ^ 2)]
      rw [div_eq_mul_inv]
      calc
        ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) < 2 * ‖x‖ := hdenom_lt_two_r
        _ < 2 * δ := by nlinarith
        _ = 1 / (2 * ((C : ℝ) + 1)) := by
          dsimp [δ]
          (field_simp; ring)
        _ < 1 / ((C : ℝ) + 1) := by
          rw [div_lt_div_iff₀ (by positivity) hC1]
          nlinarith
    have hC_mul_lt : (C : ℝ) * (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2)) < 1 := by
      have hC0 : 0 ≤ (C : ℝ) := C.coe_nonneg
      have hC1 : 0 < (C : ℝ) + 1 := by positivity
      calc
        (C : ℝ) * (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2))
            ≤ (C : ℝ) * (1 / ((C : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left hdenom_lt.le hC0
        _ < 1 := by
          rw [one_div, ← div_eq_mul_inv]
          exact (div_lt_one hC1).2 (by linarith)
    have hlarge : (C : ℝ) < ‖f_radial x‖ := by
      rw [f_radial, if_neg hx0, Real.norm_eq_abs,
        abs_of_pos (mul_pos (sq_pos_of_pos (inv_pos.mpr hr0))
          (inv_pos.mpr (by positivity)))]
      have hformula :
          ‖x‖⁻¹ ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ =
            (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2))⁻¹ := by
        field_simp
      rw [hformula, ← one_div]
      exact (lt_div_iff₀ hdenom_pos).2 hC_mul_lt
    have hxC' : ‖f_radial x‖ ≤ (C : ℝ) := by exact_mod_cast hxC
    exact (not_lt_of_ge hxC') hlarge
  have hball_zero : volume (Metric.ball (0 : E) δ) = 0 := by
    simpa only [ae_iff, not_not] using hout
  exact (Metric.measure_ball_pos volume (0 : E) hδ).ne' hball_zero

/-- f is in L^1(R^3), since its radial density simplifies to
`(1 + r²)⁻¹`, which is integrable on `(0, ∞)`. -/
theorem f_radial_integrable :
    Integrable f_radial volume := by
  let profile : ℝ → ℝ := fun r =>
    if r = 0 then 0 else r⁻¹ ^ 2 * (1 + r ^ 2)⁻¹
  have hradial : f_radial = fun x : E => profile ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · simp [f_radial, profile, hx]
    · simp [f_radial, profile, hx, norm_ne_zero_iff.mpr hx]
  rw [hradial,
    ConstructionTargets.RadialIntegrationR3.integrable_radial_R3_iff]
  refine integrable_inv_one_add_sq.integrableOn.congr_fun ?_ measurableSet_Ioi
  intro r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  simp only [profile, if_neg hr0]
  field_simp

/-- Young's inequality: ||phi * g||_2 <= ||phi||_1 * ||g||_2.

This is the special case 1/2 = 1/1 + 1/2 - 1 of Young's convolution inequality.

**Blocker:** Young's inequality for convolutions is not proved in Mathlib.
The file `Mathlib.Analysis.Convolution` defines the convolution and proves
basic properties (integrability of the integrand, continuity, support),
but the Lp norm inequality is absent.

A genuine proof would use Minkowski's integral inequality combined with
translation invariance of the L^2 norm, or the generalized Holder inequality
for mixed-norm spaces. -/
lemma young_inequality_L1_L2
    (φ : E → ℝ) (hφ : Integrable φ volume)
    (g : E → ℝ) (hg : MemLp g 2 volume) :
    eLpNorm (fun x => ∫ y, φ (x - y) * g y ∂volume) 2 volume ≤
      eLpNorm φ 1 volume * eLpNorm g 2 volume := by
  have hpoint (x : E) :
      ‖∫ y, φ (x - y) * g y ∂volume‖ₑ ^ 2 ≤
        (∫⁻ y, ‖φ y‖ₑ ∂volume) *
          (∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ^ 2 ∂volume) := by
    have hφ_x : AEMeasurable (fun y : E => ‖φ (x - y)‖ₑ) volume :=
      ((hφ.aestronglyMeasurable.comp_measurePreserving
        (Measure.measurePreserving_sub_left (volume : Measure E) x)).enorm)
    have hg_enorm : AEMeasurable (fun y : E => ‖g y‖ₑ) volume :=
      hg.aestronglyMeasurable.enorm
    have hnorm :
        ‖∫ y, φ (x - y) * g y ∂volume‖ₑ ≤
          ∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ∂volume := by
      refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
      apply lintegral_congr
      intro y
      simp [enorm_mul]
    calc
      ‖∫ y, φ (x - y) * g y ∂volume‖ₑ ^ 2
          ≤ (∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ∂volume) ^ 2 :=
        pow_le_pow_left₀ (zero_le _) hnorm 2
      _ ≤ (∫⁻ y, ‖φ (x - y)‖ₑ ∂volume) *
          (∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ^ 2 ∂volume) :=
        lintegral_weight_mul_sq_le _ _ hφ_x hg_enorm
      _ = (∫⁻ y, ‖φ y‖ₑ ∂volume) *
          (∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ^ 2 ∂volume) := by
        congr 1
        let mp := Measure.measurePreserving_sub_left (volume : Measure E) x
        have hφ_comp : Integrable (fun t => φ (x - t)) volume := by
          simpa [Function.comp_def] using mp.integrable_comp_of_integrable hφ
        rw [← ofReal_integral_norm_eq_lintegral_enorm hφ_comp,
          ← ofReal_integral_norm_eq_lintegral_enorm hφ]
        congr 1
        exact integral_sub_left_eq_self (fun y => ‖φ y‖) (volume : Measure E) x
  let Φ : ℝ≥0∞ := ∫⁻ y, ‖φ y‖ₑ ∂volume
  let G2 : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ ^ 2 ∂volume
  have hΦ_top : Φ ≠ ∞ := ne_of_lt hφ.hasFiniteIntegral
  have h_joint : AEMeasurable
      (Function.uncurry fun x y : E =>
        ‖φ (x - y)‖ₑ * ‖g y‖ₑ ^ 2)
      (volume.prod volume) := by
    have hφ_joint : AEMeasurable
        (fun z : E × E => ‖φ (z.1 - z.2)‖ₑ)
        (volume.prod volume) := by
      simpa [Function.comp_def] using
        (hφ.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub (volume : Measure E) volume))
    exact hφ_joint.mul (hg.aestronglyMeasurable.enorm.comp_snd.pow_const _)
  have hdouble :
      (∫⁻ x, ‖∫ y, φ (x - y) * g y ∂volume‖ₑ ^ 2 ∂volume) ≤
        Φ ^ 2 * G2 := by
    calc
      (∫⁻ x, ‖∫ y, φ (x - y) * g y ∂volume‖ₑ ^ 2 ∂volume)
          ≤ ∫⁻ x, Φ *
              (∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ^ 2 ∂volume) ∂volume := by
            apply lintegral_mono
            intro x
            exact hpoint x
      _ = Φ * (∫⁻ x,
              (∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ^ 2 ∂volume) ∂volume) := by
            rw [lintegral_const_mul' Φ _ hΦ_top]
      _ = Φ * (∫⁻ y,
              (∫⁻ x, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ^ 2 ∂volume) ∂volume) := by
            rw [lintegral_lintegral_swap h_joint]
      _ = Φ * (Φ * G2) := by
            congr 1
            calc
              (∫⁻ y, (∫⁻ x, ‖φ (x - y)‖ₑ * ‖g y‖ₑ ^ 2 ∂volume) ∂volume)
                  = ∫⁻ y, Φ * ‖g y‖ₑ ^ 2 ∂volume := by
                    apply lintegral_congr
                    intro y
                    rw [lintegral_mul_const' _ _ (by finiteness)]
                    congr 1
                    simpa [Φ, sub_eq_add_neg] using
                      lintegral_add_right_eq_self (μ := volume)
                        (fun x : E => ‖φ x‖ₑ) (-y)
              _ = Φ * G2 := by
                    rw [lintegral_const_mul' Φ _ hΦ_top]
      _ = Φ ^ 2 * G2 := by ring
  have hroot :
      (∫⁻ x, ‖∫ y, φ (x - y) * g y ∂volume‖ₑ ^ (2 : ℝ) ∂volume) ^
          (1 / 2 : ℝ) ≤
        Φ * G2 ^ (1 / 2 : ℝ) := by
    calc
      (∫⁻ x, ‖∫ y, φ (x - y) * g y ∂volume‖ₑ ^ (2 : ℝ) ∂volume) ^
            (1 / 2 : ℝ)
          ≤ (Φ ^ 2 * G2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (by simpa [ENNReal.rpow_two] using hdouble) (by norm_num)
      _ = Φ * G2 ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simpa [Φ, G2] using hroot

/-- Part (c): For g in L^2(R^3), f * g in L^2(R^3) with
  ||f * g||_2 <= 2 * pi^2 * ||g||_2.

By Young's convolution inequality: ||f * g||_2 <= ||f||_1 * ||g||_2.
From part (b), ||f||_1 = 2*pi^2, so c = 2*pi^2. -/
theorem f_radial_conv_L2_bound
    {g : E → ℝ}
    (hg : MemLp g 2 volume) :
    eLpNorm (fun x => ∫ y, f_radial (x - y) * g y ∂volume) 2 volume ≤
      ENNReal.ofReal (2 * π ^ 2) * eLpNorm g 2 volume := by
  have hnonneg : ∀ x : E, 0 ≤ f_radial x := by
    intro x
    simp only [f_radial]
    split_ifs
    · exact le_rfl
    · positivity
  have hnorm : eLpNorm f_radial 1 volume = ENNReal.ofReal (2 * π ^ 2) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm f_radial_integrable]
    congr 1
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using
      f_radial_integral
  rw [← hnorm]
  exact young_inequality_L1_L2 f_radial f_radial_integrable g hg

/-- Spherical coordinate reduction in R^3:
  integral_{R^3} g(|x|) dx = 4*pi * integral_0^inf g(r) r^2 dr.

The surface area of S^2 is 4*pi.

**Blocker:** This formula is not directly available in Mathlib.
A proof would use the coarea formula or layer cake representation,
combined with the fact that the surface measure of S^{n-1} in R^n
has total mass 2*pi^{n/2}/Gamma(n/2), which for n = 3 gives 4*pi. -/
lemma radial_integral_R3 {g : ℝ → ℝ}
    (hg : Integrable (fun x : E => g ‖x‖) volume) :
    ∫ x : E, g ‖x‖ ∂volume =
      4 * π * ∫ r in Ioi (0:ℝ), g r * r ^ 2 ∂volume := by
  exact ConstructionTargets.RadialIntegrationR3.radial_integral_R3 hg

/-- f_radial equals |x|^{-2}(1+|x|^2)^{-1} away from the origin. -/
lemma f_radial_eq_of_ne_zero
    (x : E) (hx : x ≠ 0) :
    f_radial x = ‖x‖⁻¹ ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ := by
  rw [f_radial]
  split_ifs with h
  · exact absurd h hx
  · rfl

end
