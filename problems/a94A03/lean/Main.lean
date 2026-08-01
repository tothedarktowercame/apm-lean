import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import ConstructionTargets.L2Translation
import ConstructionTargets.YoungConvolution

/-!
# APM a94A03: Gaussian convolution is an Lp contraction and approximate identity

**Problem.** For f in Lp(R) with 1 <= p < infinity and t > 0, define
K_t(f)(x) = (1/t) integral of e^{-pi(x-y)^2/t^2} f(y) dy.
(a) K_t maps the unit ball of Lp into itself.
(b) K_t f converges to f in Lp norm as t -> 0.

## Statement repair note

Mathlib does not have Young's convolution inequality.  It does have continuity
of translations in `Lp`, via `Continuous.compMeasurePreservingLp`; the remaining
gap is the probability-kernel estimate needed to use that continuity here.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology

namespace ApmCanaries.A94A03

/-- The Gaussian kernel phi_t(x) = (1/t) e^{-pi x^2/t^2}. -/
noncomputable def gaussKernel (t x : ℝ) : ℝ :=
  (1 / t) * exp (-π * x ^ 2 / t ^ 2)

/-- The Gaussian convolution operator K_t f(x) = integral phi_t(x-y) f(y) dy. -/
noncomputable def gaussConv (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, gaussKernel t (x - y) * f y ∂volume

/-- The Gaussian kernel is nonneg. -/
lemma gaussKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ gaussKernel t x := by
  unfold gaussKernel
  positivity

/-- The Gaussian kernel integrates to 1. -/
lemma gaussKernel_integral_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ x, gaussKernel t x ∂volume = 1 := by
  unfold gaussKernel
  rw [integral_const_mul]
  have hcoeff : ∀ x : ℝ, -π * x ^ 2 / t ^ 2 = -(π / t ^ 2) * x ^ 2 := by
    intro x
    ring
  simp_rw [hcoeff]
  rw [integral_gaussian]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  rw [show π / (π / t ^ 2) = t ^ 2 by field_simp]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  field_simp

/-- The Gaussian kernel is integrable. -/
lemma gaussKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (gaussKernel t) volume := by
  by_contra h
  have hone := gaussKernel_integral_eq_one ht
  rw [integral_undef h] at hone
  norm_num at hone

/-- A positive-scale Gaussian is the pullback of the unit Gaussian under dilation. -/
lemma gaussKernel_scale {t : ℝ} (ht : 0 < t) (x : ℝ) :
    t * gaussKernel t (t * x) = gaussKernel 1 x := by
  unfold gaussKernel
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp

/-- The Gaussian kernel is even. -/
lemma gaussKernel_neg (t x : ℝ) :
    gaussKernel t (-x) = gaussKernel t x := by
  unfold gaussKernel
  congr 2
  ring

/-- After dilation, convolution by a Gaussian of scale `t` is averaging translates against the
fixed unit Gaussian. -/
lemma gaussConv_eq_integral_unitKernel {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) :
    gaussConv t f x = ∫ z, gaussKernel 1 z * f (x - t * z) ∂volume := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [gaussConv]
  have hsub :
      (∫ y : ℝ, gaussKernel t (x - y) * f y ∂volume) =
        ∫ u : ℝ, gaussKernel t u * f (x - u) ∂volume := by
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self (fun u : ℝ ↦ gaussKernel t u * f (x - u)) volume x)
  rw [hsub]
  have hscale := Measure.integral_comp_mul_left
    (fun u : ℝ ↦ gaussKernel t u * f (x - u)) t
  simp only [abs_inv, abs_of_pos ht] at hscale
  calc
    (∫ u : ℝ, gaussKernel t u * f (x - u) ∂volume) =
        t * ∫ z : ℝ, gaussKernel t (t * z) * f (x - t * z) ∂volume := by
          rw [hscale]
          simp [ht0]
    _ = ∫ z : ℝ, t * (gaussKernel t (t * z) * f (x - t * z)) ∂volume := by
          rw [integral_const_mul]
    _ = ∫ z : ℝ, gaussKernel 1 z * f (x - t * z) ∂volume := by
          apply integral_congr_ae
          filter_upwards with z
          rw [← mul_assoc, gaussKernel_scale ht]


/-- Part (a): K_t is an Lp contraction: eLpNorm(K_t f) <= eLpNorm(f).

    This is Young's convolution inequality with the normalized positive
    Gaussian as the `L¹` factor. -/
theorem gaussConv_Lp_contraction
    {p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : MemLp f p volume) :
    eLpNorm (gaussConv t f) p volume ≤ eLpNorm f p volume := by
  have hkernel_norm : eLpNorm (gaussKernel t) 1 volume = 1 := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (gaussKernel_integrable ht)]
    have hint : ∫ x, ‖gaussKernel t x‖ ∂volume = 1 := by
      calc
        (∫ x, ‖gaussKernel t x‖ ∂volume) =
            ∫ x, gaussKernel t x ∂volume := by
              apply integral_congr_ae
              filter_upwards with x
              rw [Real.norm_eq_abs, abs_of_nonneg (gaussKernel_nonneg ht x)]
        _ = 1 := gaussKernel_integral_eq_one ht
    rw [hint]
    norm_num
  have hyoung :=
    ConstructionTargets.YoungConvolution.young_convolution_inequality
      hp hp' (gaussKernel_integrable ht) hf
  change eLpNorm (ConstructionTargets.YoungConvolution.convolution
    (gaussKernel t) f) p volume ≤ eLpNorm f p volume
  simpa [hkernel_norm] using hyoung

/-- Part (b): K_t f converges to f in Lp as t -> 0+.

    SORRY BOUNDARY: translation continuity and Young contraction are now
    available.  The remaining reusable gap is the Banach-valued Minkowski
    estimate for the average of translation differences; after it, split the
    unit Gaussian into a compact head (uniform translation continuity) and an
    integrable tail (bounded by twice the `Lp` norm). -/
theorem gaussConv_tendsto_Lp
    {p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun t => eLpNorm (fun x => gaussConv t f x - f x) p volume)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

end ApmCanaries.A94A03
