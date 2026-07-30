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

1. Spherical coordinate reduction for radial integrals in R^3 (parts a, b)
2. Young's convolution inequality for Lp norms (part c)
Neither is available in Mathlib.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import ConstructionTargets.RadialIntegrationR3

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
  sorry

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
  sorry

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

/-- Part (c): For g in L^2(R^3), f * g in L^2(R^3) with
  ||f * g||_2 <= 2 * pi^2 * ||g||_2.

By Young's convolution inequality: ||f * g||_2 <= ||f||_1 * ||g||_2.
From part (b), ||f||_1 = 2*pi^2, so c = 2*pi^2.

**Blocker:** Young's convolution inequality is not proved in Mathlib.
The convolution operator is defined in `Mathlib.Analysis.Convolution`
but the Lp norm bound is absent.

This sorry inherits from `f_radial_integral` and `young_inequality_L1_L2`. -/
theorem f_radial_conv_L2_bound
    {g : E → ℝ}
    (hg : MemLp g 2 volume) :
    eLpNorm (fun x => ∫ y, f_radial (x - y) * g y ∂volume) 2 volume ≤
      ENNReal.ofReal (2 * π ^ 2) * eLpNorm g 2 volume := by
  sorry

/-- f is in L^1(R^3), since 3/4 < 1 < 3/2 (from part a).

Inherits the sorry from part (a). -/
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
  sorry

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
