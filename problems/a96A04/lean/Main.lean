/-
! # APM a96A04: Heat kernel — smoothness, L² contraction, L² convergence

u(x,t) = (4πt)^{-n/2} ∫ e^{-|x-y|²/(4t)} f(y) dy (heat kernel convolution).
(a) u is smooth in x for t > 0.
(b) ‖u(·,t)‖₂ ≤ ‖f‖₂.
(c) u(·,t) → f in L² as t → 0⁺.

## Theory boundaries

- Young's convolution inequality is NOT in Mathlib (blocks part b).
- The heat kernel normalization (∫G_t = 1) requires the Gaussian integral.
- Differentiation under the integral sign requires DCT machinery (part a).
- The Fourier approach requires Fourier transform of Gaussian (parts b, c).

## Statement repair

We use ℝ (the 1D case) to avoid EuclideanSpace measure issues. The
mathematical content generalizes to ℝⁿ but the formalization is cleaner
in 1D. The generated `Memℒp` is corrected to `MemLp`.
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import ConstructionTargets.L2Translation
import ConstructionTargets.LpRepresentative
import ConstructionTargets.YoungConvolution
import YoungL2

open MeasureTheory Set Filter Real Topology

open scoped ENNReal ContDiff

noncomputable section

/-- The heat kernel G_t(x) = (4πt)^{-1/2} exp(-x²/(4t)) for t > 0 (1D). -/
def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (- x ^ 2 / (4 * t))

/-- The heat convolution u(x,t) = (G_t * f)(x) = ∫ G_t(x-y) f(y) dy. -/
def heatConv (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, heatKernel t (x - y) * f y ∂volume

/-- A positive-time heat kernel is nonnegative. -/
lemma heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ heatKernel t x := by
  unfold heatKernel
  positivity

/-- The heat kernel integrates to 1 (1D).

∫ G_t(x) dx = (4πt)^{-1/2} ∫ e^{-x²/(4t)} dx = (4πt)^{-1/2} · √(4πt) = 1.

**Blocker:** Requires the 1D Gaussian integral ∫₀^∞ e^{-ax²} dx = √(π)/(2√a). -/
lemma heatKernel_integral {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, heatKernel t x ∂volume = 1 := by
  have h_pos : 0 < 4 * π * t := by positivity
  have h_gauss : ∫ x : ℝ, Real.exp (-(1 / (4 * t)) * x ^ 2) = Real.sqrt (4 * π * t) := by
    have := integral_gaussian (1 / (4 * t))
    rwa [show π / (1 / (4 * t)) = 4 * π * t from by field_simp] at this
  -- ∫ heatKernel t x dx = ∫ prefactor · exp(...) dx = prefactor · ∫ exp(...) dx
  rw [show heatKernel t = fun x => (4 * π * t) ^ (-(1:ℝ) / 2) * Real.exp (-(1 / (4 * t)) * x ^ 2) from
    funext fun x => by unfold heatKernel; field_simp]
  rw [integral_const_mul, h_gauss]
  -- (4πt)^{-1/2} · √(4πt) = 1
  have h_key : (4 * π * t) ^ (-(1:ℝ) / 2) * (4 * π * t) ^ ((1:ℝ) / 2) = 1 := by
    rw [← Real.rpow_add h_pos]
    show (4 * π * t) ^ (-(1:ℝ) / 2 + (1:ℝ) / 2) = 1
    rw [show -(1:ℝ) / 2 + 1 / 2 = 0 by ring, Real.rpow_zero]
  convert h_key using 2
  · exact Real.sqrt_eq_rpow (4 * π * t)

/-- A positive-time heat kernel is integrable. -/
lemma heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel t) volume := by
  by_contra h
  have hone := heatKernel_integral ht
  rw [integral_undef h] at hone
  norm_num at hone

/-- For positive time, the heat kernel itself is smooth.  This isolates the
regularity input needed by a future non-compact-support convolution theorem. -/
lemma heatKernel_contDiff {t : ℝ} (_ht : 0 < t) :
    ContDiff ℝ ∞ (heatKernel t) := by
  unfold heatKernel
  fun_prop

/-- The first derivative of the positive-time heat kernel. -/
lemma heatKernel_hasDerivAt {t x : ℝ} (_ht : 0 < t) :
    HasDerivAt (heatKernel t) (-(x / (2 * t)) * heatKernel t x) x := by
  have harg : HasDerivAt (fun y : ℝ => -y ^ 2 / (4 * t)) (-(2 * x) / (4 * t)) x := by
    convert (((hasDerivAt_id x).pow 2).neg.div_const (4 * t)) using 1
    all_goals simp only [id_eq]; ring
  have h := harg.exp.const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  convert h using 1
  all_goals simp only [heatKernel]; ring

/-- Pointwise derivative formula for the positive-time heat kernel. -/
lemma heatKernel_deriv {t x : ℝ} (ht : 0 < t) :
    deriv (heatKernel t) x = -(x / (2 * t)) * heatKernel t x :=
  (heatKernel_hasDerivAt ht).deriv

/-- The first derivative of a positive-time heat kernel is integrable. -/
lemma heatKernel_deriv_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => -(x / (2 * t)) * heatKernel t x) volume := by
  have hbase : Integrable
      (fun x : ℝ => x * Real.exp (-(1 / (4 * t)) * x ^ 2)) volume :=
    integrable_mul_exp_neg_mul_sq (by positivity)
  apply (hbase.const_mul
    (-((4 * π * t) ^ (-(1 : ℝ) / 2)) / (2 * t))).congr
  filter_upwards with x
  have hexp : -x ^ 2 / (4 * t) = -(1 / (4 * t)) * x ^ 2 := by ring
  rw [show heatKernel t x =
      (4 * π * t) ^ (-(1 : ℝ) / 2) *
        Real.exp (-(1 / (4 * t)) * x ^ 2) by simp [heatKernel, hexp]]
  ring

/-- Every monomial times a decaying Gaussian is integrable.  This is the
finite-sum building block needed for the Hermite-polynomial description of
all spatial derivatives of the heat kernel. -/
lemma integrable_pow_mul_exp_neg_mul_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-b * x ^ 2)) volume := by
  have hn : (-1 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have h := integrable_rpow_mul_exp_neg_mul_sq hb hn
  have hm : AEStronglyMeasurable
      (fun x : ℝ => x ^ n * Real.exp (-b * x ^ 2)) volume := by
    fun_prop
  apply (integrable_norm_iff hm).mp
  apply h.norm.congr
  filter_upwards with x
  rw [Real.rpow_natCast]

/-- A polynomial factor does not destroy Gaussian integrability. -/
lemma integrable_polynomial_mul_exp_neg_mul_sq
    (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) volume := by
  rw [show (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) =
      fun x => ∑ n ∈ Finset.range (p.natDegree + 1),
        p.coeff n * (x ^ n * Real.exp (-b * x ^ 2)) by
    funext x
    rw [Polynomial.eval_eq_sum_range]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    ring]
  exact integrable_finset_sum _ fun n _ =>
    (integrable_pow_mul_exp_neg_mul_sq n hb).const_mul (p.coeff n)

/-- All iterated derivatives of the standard Gaussian are integrable.  The
Hermite formula supplies the polynomial factor, and the preceding lemma
supplies the analytic domination. -/
lemma integrable_iterate_deriv_standardGaussian (n : ℕ) :
    Integrable (deriv^[n] (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))) volume := by
  let p : Polynomial ℝ :=
    (Polynomial.hermite n).map (Int.castRingHom ℝ)
  have h := integrable_polynomial_mul_exp_neg_mul_sq p
    (show (0 : ℝ) < 1 / 2 by norm_num)
  apply (h.const_mul ((-1 : ℝ) ^ n)).congr
  filter_upwards with x
  rw [Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
  rw [show p.eval x = Polynomial.aeval x (Polynomial.hermite n) by
    exact Polynomial.eval_map (p := Polynomial.hermite n)
      (f := Int.castRingHom ℝ) x]
  rw [show -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2 / 2) by ring]
  ring

/-- A positive-time heat kernel is square-integrable. -/
lemma heatKernel_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp (heatKernel t) 2 volume := by
  refine (memLp_two_iff_integrable_sq
    (heatKernel_contDiff ht).continuous.aestronglyMeasurable).2 ?_
  have hgauss : Integrable (fun x : ℝ => Real.exp (-(1 / (2 * t)) * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq (by positivity)
  convert hgauss.const_mul (((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ 2) using 1
  funext x
  unfold heatKernel
  have hexp :
      Real.exp (-x ^ 2 / (4 * t)) ^ 2 =
        Real.exp (-(1 / (2 * t)) * x ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hexp]

/-- A positive-time heat kernel is obtained from the time-one kernel by
dilation.  This is the normalization used in the approximate-identity
argument below. -/
lemma heatKernel_scale {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.sqrt t * heatKernel t (Real.sqrt t * x) = heatKernel 1 x := by
  have hsqrt : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  unfold heatKernel
  rw [mul_pow, hsqrt_sq]
  have hcoeff :
      Real.sqrt t * (4 * π * t) ^ (-(1 : ℝ) / 2) =
        (4 * π) ^ (-(1 : ℝ) / 2) := by
    rw [show 4 * π * t = (4 * π) * t by ring,
      Real.mul_rpow (by positivity : 0 ≤ (4 : ℝ) * π) ht.le,
      Real.sqrt_eq_rpow]
    calc
      t ^ (1 / 2 : ℝ) *
          ((4 * π) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2)) =
          (4 * π) ^ (-(1 : ℝ) / 2) *
            (t ^ (1 / 2 : ℝ) * t ^ (-(1 : ℝ) / 2)) := by ring
      _ = (4 * π) ^ (-(1 : ℝ) / 2) := by
        rw [← Real.rpow_add ht]
        norm_num
  rw [← mul_assoc, hcoeff]
  simp only [mul_one]
  congr 1
  apply congrArg Real.exp
  field_simp

/-- After dilation, heat convolution is averaging translates against the
fixed time-one heat kernel. -/
lemma heatConv_eq_integral_unitKernel {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℝ) (x : ℝ) :
    heatConv t f x =
      ∫ z, heatKernel 1 z * f (x - Real.sqrt t * z) ∂volume := by
  have hsqrt : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  unfold heatConv
  have hsub :
      (∫ y : ℝ, heatKernel t (x - y) * f y ∂volume) =
        ∫ u : ℝ, heatKernel t u * f (x - u) ∂volume := by
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self
        (fun u : ℝ ↦ heatKernel t u * f (x - u)) volume x)
  rw [hsub]
  have hscale := Measure.integral_comp_mul_left
    (fun u : ℝ ↦ heatKernel t u * f (x - u)) (Real.sqrt t)
  simp only [abs_inv, abs_of_pos (Real.sqrt_pos.2 ht)] at hscale
  calc
    (∫ u : ℝ, heatKernel t u * f (x - u) ∂volume) =
        Real.sqrt t * ∫ z : ℝ,
          heatKernel t (Real.sqrt t * z) *
            f (x - Real.sqrt t * z) ∂volume := by
      rw [hscale]
      simp [hsqrt]
    _ = ∫ z : ℝ, Real.sqrt t *
          (heatKernel t (Real.sqrt t * z) *
            f (x - Real.sqrt t * z)) ∂volume := by
      rw [integral_const_mul]
    _ = ∫ z : ℝ, heatKernel 1 z *
          f (x - Real.sqrt t * z) ∂volume := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← mul_assoc, heatKernel_scale ht]

/-- The fixed-Gaussian average of translation differences tends to zero in
the abstract `L²` space.  The remaining pointwise theorem only has to identify
this Bochner integral with the class represented by `heatConv t f - f`. -/
lemma heat_translation_average_tendsto_L2
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    let τ : ℝ → C(ℝ, ℝ) := fun s =>
      ⟨fun x => x - s, continuous_id.sub continuous_const⟩
    let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
      simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
    let F : ℝ → Lp ℝ 2 volume := fun s =>
      Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
    Tendsto
      (fun s => ∫ z, heatKernel 1 z • (F (s * z) - F 0) ∂volume)
      (𝓝 0) (𝓝 0) := by
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  have hτc : Continuous τ := by
    let G : C(ℝ × ℝ, ℝ) :=
      ⟨fun z => z.2 - z.1, continuous_snd.sub continuous_fst⟩
    exact (ContinuousMap.curry G).continuous
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ 2 volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  have hFc : Continuous F := by
    dsimp [F]
    exact continuous_const.compMeasurePreservingLp hτc hτ (by norm_num)
  have hkcont : Continuous (heatKernel 1) :=
    (heatKernel_contDiff (by norm_num)).continuous
  have hkint : Integrable (heatKernel 1) volume :=
    heatKernel_integrable (by norm_num)
  have hbound_int : Integrable
      (fun z => heatKernel 1 z * (2 * ‖hf.toLp f‖)) volume :=
    hkint.mul_const _
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 (0 : ℝ)) (μ := volume)
    (F := fun s z => heatKernel 1 z • (F (s * z) - F 0))
    (f := fun _ => (0 : Lp ℝ 2 volume))
    (fun z => heatKernel 1 z * (2 * ‖hf.toLp f‖))
  have hmeas : ∀ᶠ s : ℝ in 𝓝 0,
      AEStronglyMeasurable
        (fun z => heatKernel 1 z • (F (s * z) - F 0)) volume := by
    filter_upwards with s
    exact (hkcont.smul
      ((hFc.comp (continuous_const.mul continuous_id)).sub
        continuous_const)).aestronglyMeasurable
  have hbound : ∀ᶠ s : ℝ in 𝓝 0, ∀ᵐ z : ℝ ∂volume,
      ‖heatKernel 1 z • (F (s * z) - F 0)‖ ≤
        heatKernel 1 z * (2 * ‖hf.toLp f‖) := by
    filter_upwards with s
    filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (heatKernel_nonneg (by norm_num) z)]
    apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg (by norm_num) z)
    calc
      ‖F (s * z) - F 0‖ ≤ ‖F (s * z)‖ + ‖F 0‖ := norm_sub_le _ _
      _ = 2 * ‖hf.toLp f‖ := by
        simp only [F, Lp.norm_compMeasurePreserving]
        ring
  have hlim : ∀ᵐ z : ℝ ∂volume,
      Tendsto (fun s => heatKernel 1 z • (F (s * z) - F 0))
        (𝓝 0) (𝓝 0) := by
    filter_upwards with z
    have hsz : Tendsto (fun s : ℝ => s * z) (𝓝 0) (𝓝 0) := by
      simpa using tendsto_id.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => z) (𝓝 0) (𝓝 z))
    have hsub : Tendsto (fun s => F (s * z) - F 0) (𝓝 0) (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self] using
        ((hFc.tendsto 0).comp hsz).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => F 0) (𝓝 0) (𝓝 (F 0)))
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => heatKernel 1 z)
        (𝓝 0) (𝓝 (heatKernel 1 z))).smul hsub
  simpa only [integral_zero] using hdct hmeas hbound hbound_int hlim

/-- Rewrite heat convolution as a heat-kernel average of translates of `f`.

This is the change-of-variables seam used by the `L²` approximate-identity
argument. -/
lemma heatConv_eq_integral_translation
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    heatConv t f x = ∫ y, heatKernel t y * f (x - y) ∂volume := by
  unfold heatConv
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self
      (fun y : ℝ ↦ heatKernel t y * f (x - y)) volume x)

/-- (a) u(·,t) is smooth in x for t > 0.

The regularity index `∞ : WithTop ℕ∞` states `C^∞` smoothness, matching the
problem, rather than the analytic regularity denoted by `⊤`. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): use `∞` for smoothness;
-- after Mathlib's index-type migration, `⊤` denotes analytic regularity.
theorem heatConv_contDiff
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (heatConv t f) := by
  have hfloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  -- `ContDiff.Convolution` only packages this implication when the smooth
  -- factor has compact support.  The Hermite lemmas above now provide the
  -- required integrability for every Gaussian derivative.  It remains to
  -- transport them through the heat-kernel scaling and iterate the local
  -- dominated parametric-integral differentiation theorem.
  sorry

/-- (b) L² contraction: ‖u(·,t)‖₂ ≤ ‖f‖₂.

The repository's axiom-clean `YoungL2` module supplies the required
`L¹ * L² → L²` estimate. -/
theorem heatConv_L2_le
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    eLpNorm (heatConv t f) 2 volume ≤
      eLpNorm f 2 volume := by
  apply convolution_L2_contraction_of_probability_kernel
  · exact heatKernel_nonneg ht
  · exact heatKernel_integral ht
  · exact hf

/-- Positive-time heat convolution preserves `L²` membership. -/
lemma heatConv_memLp
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (heatConv t f) 2 volume := by
  change MemLp
    (ConstructionTargets.YoungConvolution.convolution (heatKernel t) f) 2 volume
  exact ConstructionTargets.YoungConvolution.convolution_memLp
    (by norm_num) (by norm_num) (heatKernel_integrable ht) hf

/-- The abstract heat-kernel average has pointwise representative
`heatConv t f - f`. -/
lemma heat_translation_average_toLp
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    let τ : ℝ → C(ℝ, ℝ) := fun s =>
      ⟨fun x => x - s, continuous_id.sub continuous_const⟩
    let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
      simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
    let F : ℝ → Lp ℝ 2 volume := fun s =>
      Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
    let G : ℝ → Lp ℝ 2 volume := fun z =>
      heatKernel 1 z • (F (Real.sqrt t * z) - F 0)
    ((heatConv_memLp ht hf).sub hf).toLp
        (fun x => heatConv t f x - f x) = ∫ z, G z ∂volume := by
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  have hτc : Continuous τ := by
    let T : C(ℝ × ℝ, ℝ) :=
      ⟨fun z => z.2 - z.1, continuous_snd.sub continuous_fst⟩
    exact (ContinuousMap.curry T).continuous
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ 2 volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  let G : ℝ → Lp ℝ 2 volume := fun z =>
    heatKernel 1 z • (F (Real.sqrt t * z) - F 0)
  let φ : ℝ × ℝ → ℝ := fun z =>
    heatKernel 1 z.1 * (f (z.2 - Real.sqrt t * z.1) - f z.2)
  have hFc : Continuous F := by
    dsimp [F]
    exact continuous_const.compMeasurePreservingLp hτc hτ (by norm_num)
  have hkcont : Continuous (heatKernel 1) :=
    (heatKernel_contDiff (by norm_num)).continuous
  have hGc : Continuous G := by
    dsimp [G]
    exact hkcont.smul
      ((hFc.comp (continuous_const.mul continuous_id)).sub continuous_const)
  have hG : Integrable G volume := by
    have hdom : Integrable
        (fun z => heatKernel 1 z * (2 * ‖hf.toLp f‖)) volume :=
      (heatKernel_integrable (by norm_num)).mul_const _
    refine hdom.mono' hGc.aestronglyMeasurable ?_
    filter_upwards with z
    change ‖heatKernel 1 z • (F (Real.sqrt t * z) - F 0)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (heatKernel_nonneg (by norm_num) z)]
    apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg (by norm_num) z)
    calc
      ‖F (Real.sqrt t * z) - F 0‖ ≤
          ‖F (Real.sqrt t * z)‖ + ‖F 0‖ := norm_sub_le _ _
      _ = 2 * ‖hf.toLp f‖ := by
        simp only [F, Lp.norm_compMeasurePreserving]
        ring
  have hsqrt : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hqmp : Measure.QuasiMeasurePreserving
      (fun z : ℝ × ℝ => z.2 - Real.sqrt t * z.1)
      (volume.prod volume) volume := by
    refine QuasiMeasurePreserving.prod_of_left (by fun_prop) ?_
    filter_upwards with x
    have hscale : Measure.QuasiMeasurePreserving
        (fun z : ℝ => Real.sqrt t • z) volume volume :=
      Measure.quasiMeasurePreserving_smul volume hsqrt
    simpa [smul_eq_mul] using
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving.comp hscale
  have hφ : AEStronglyMeasurable φ (volume.prod volume) := by
    have hshift := hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
    have hbase := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
    have hk : AEStronglyMeasurable
        (fun z : ℝ × ℝ => heatKernel 1 z.1) (volume.prod volume) :=
      (hkcont.comp continuous_fst).aestronglyMeasurable
    exact hk.mul (hshift.sub hbase)
  have hGφ : ∀ᵐ z ∂volume,
      (G z : ℝ → ℝ) =ᵐ[volume] fun x => φ (z, x) := by
    filter_upwards with z
    filter_upwards
      [Lp.coeFn_smul (heatKernel 1 z) (F (Real.sqrt t * z) - F 0),
       Lp.coeFn_sub (F (Real.sqrt t * z)) (F 0),
       Lp.coeFn_compMeasurePreserving (hf.toLp f) (hτ (Real.sqrt t * z)),
       Lp.coeFn_compMeasurePreserving (hf.toLp f) (hτ 0),
       (hτ (Real.sqrt t * z)).quasiMeasurePreserving.ae hf.coeFn_toLp,
       (hτ 0).quasiMeasurePreserving.ae hf.coeFn_toLp]
      with x hsmul hsub htrans hzero hrept hrepzero
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [htrans, hzero]
    simp only [Function.comp_apply]
    rw [hrept, hrepzero]
    simp [φ, τ]
  have hlocal : ∀ s : Set ℝ, MeasurableSet s → volume s ≠ ⊤ →
      HasFiniteIntegral
        (fun z : ℝ × ℝ => s.indicator (fun x => φ (z.1, x)) z.2)
        (volume.prod volume) :=
    ConstructionTargets.LpRepresentative.hasFiniteIntegral_indicator_lift
      hφ hG hGφ
  have hslice : ∀ᵐ x ∂volume, Integrable (fun z => φ (z, x)) volume := by
    have hn : ∀ n : ℕ, ∀ᵐ x ∂volume,
        Integrable
          (fun z => (spanningSets volume n).indicator
            (fun x => φ (z, x)) x) volume := by
      intro n
      let s : Set ℝ := spanningSets (volume : Measure ℝ) n
      have hs : MeasurableSet s := measurableSet_spanningSets (volume : Measure ℝ) n
      have hprod : Integrable
          (fun z : ℝ × ℝ => s.indicator (fun x => φ (z.1, x)) z.2)
          (volume.prod volume) := by
        exact ⟨(hφ.indicator (MeasurableSet.univ.prod hs)).congr
          (Eventually.of_forall fun z => by
            by_cases hz : z.2 ∈ s <;> simp [hz]),
          hlocal s hs (measure_spanningSets_lt_top volume n).ne⟩
      exact hprod.prod_left_ae
    filter_upwards [ae_all_iff.2 hn] with x hx
    let n := spanningSetsIndex volume x
    have hxn : x ∈ spanningSets volume n := mem_spanningSetsIndex volume x
    simpa [hxn] using hx n
  have hpoint : (fun x => ∫ z, φ (z, x) ∂volume) =ᵐ[volume]
      fun x => heatConv t f x - f x := by
    filter_upwards [hslice] with x hφx
    have hk : Integrable (fun z => heatKernel 1 z * f x) volume :=
      (heatKernel_integrable (by norm_num)).mul_const _
    have hfirst : Integrable
        (fun z => heatKernel 1 z * f (x - Real.sqrt t * z)) volume := by
      refine (hφx.add hk).congr (Eventually.of_forall fun z => ?_)
      simp [φ]
      ring
    change (∫ z, heatKernel 1 z *
      (f (x - Real.sqrt t * z) - f x) ∂volume) = heatConv t f x - f x
    rw [show (fun z => heatKernel 1 z *
        (f (x - Real.sqrt t * z) - f x)) =
        fun z => heatKernel 1 z * f (x - Real.sqrt t * z) -
          heatKernel 1 z * f x by
      funext z
      ring]
    rw [integral_sub hfirst hk, heatConv_eq_integral_unitKernel ht]
    rw [integral_mul_const, heatKernel_integral (by norm_num)]
    ring
  have hdiff : MemLp (fun x => heatConv t f x - f x) 2 volume :=
    (heatConv_memLp ht hf).sub hf
  have hψ : MemLp (fun x => ∫ z, φ (z, x) ∂volume) 2 volume :=
    (memLp_congr_ae hpoint).mpr hdiff
  have hrepr :=
    ConstructionTargets.LpRepresentative.toLp_integral_eq_integral
      (by norm_num : (2 : ENNReal) ≠ ⊤) hφ hG hGφ hlocal hψ
  exact (MemLp.toLp_congr hdiff hψ hpoint.symm).trans hrepr

/-- (c) u(·,t) → f in L² as t → 0⁺.

The contraction above supplies the density reduction.  The remaining
construction is the Gaussian approximate-identity estimate on a dense class,
or equivalently the integral-Minkowski estimate averaging continuity of
translations in `L²`; neither bridge is currently packaged in Mathlib. -/
theorem heatConv_tendsto_L2
    {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun t => eLpNorm (fun x => heatConv t f x - f x) 2 volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let τ : ℝ → C(ℝ, ℝ) := fun s =>
    ⟨fun x => x - s, continuous_id.sub continuous_const⟩
  let hτ : ∀ s, MeasurePreserving (τ s) volume volume := fun s => by
    simpa [τ, sub_eq_add_neg] using measurePreserving_add_right volume (-s)
  let F : ℝ → Lp ℝ 2 volume := fun s =>
    Lp.compMeasurePreserving (τ s) (hτ s) (hf.toLp f)
  let G : ℝ → ℝ → Lp ℝ 2 volume := fun t z =>
    heatKernel 1 z • (F (Real.sqrt t * z) - F 0)
  have havg0 : Tendsto (fun s => ∫ z, heatKernel 1 z •
      (F (s * z) - F 0) ∂volume) (nhds 0) (nhds 0) := by
    simpa [τ, hτ, F] using heat_translation_average_tendsto_L2 hf
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Real.sqrt_zero] using
      (continuous_sqrt.tendsto 0).mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  have havg : Tendsto (fun t => ∫ z, G t z ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [G] using havg0.comp hsqrt
  have henorm : Tendsto (fun t => ‖∫ z, G t z ∂volume‖ₑ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (continuous_enorm.tendsto (0 : Lp ℝ 2 volume)).comp havg
  refine henorm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hdiff : MemLp (fun x => heatConv t f x - f x) 2 volume :=
    (heatConv_memLp ht hf).sub hf
  rw [← Lp.enorm_toLp hdiff]
  congr 1
  simpa [τ, hτ, F, G] using (heat_translation_average_toLp ht hf).symm

end
