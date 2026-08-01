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
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
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

/-- Polynomial factor in the `n`th spatial derivative of the heat kernel. -/
def heatKernelDerivPoly (t : ℝ) : ℕ → Polynomial ℝ
  | 0 => Polynomial.C ((4 * π * t) ^ (-(1 : ℝ) / 2))
  | n + 1 =>
      (heatKernelDerivPoly t n).derivative -
        Polynomial.C (1 / (2 * t)) * Polynomial.X * heatKernelDerivPoly t n

/-- Replace every coefficient of a real polynomial by its absolute value. -/
def polynomialAbsCoeff (p : Polynomial ℝ) : Polynomial ℝ :=
  p.sum fun n a => Polynomial.C |a| * Polynomial.X ^ n

lemma polynomialAbsCoeff_coeff_nonneg (p : Polynomial ℝ) (n : ℕ) :
    0 ≤ (polynomialAbsCoeff p).coeff n := by
  classical
  simp only [polynomialAbsCoeff, Polynomial.coeff_sum]
  rw [Polynomial.sum]
  exact Finset.sum_nonneg fun i hi => by
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> positivity

lemma abs_polynomial_eval_le_absCoeff (p : Polynomial ℝ) (x : ℝ) :
    |p.eval x| ≤ (polynomialAbsCoeff p).eval |x| := by
  classical
  rw [Polynomial.eval_eq_sum]
  calc
    |∑ n ∈ p.support, p.coeff n * x ^ n| ≤
        ∑ n ∈ p.support, |p.coeff n * x ^ n| := Finset.abs_sum_le_sum_abs _ _
    _ = (polynomialAbsCoeff p).eval |x| := by
      rw [polynomialAbsCoeff, Polynomial.eval_sum, Polynomial.sum]
      simp [abs_mul, abs_pow]

lemma polynomial_eval_mono_of_coeff_nonneg
    {p : Polynomial ℝ} (hp : ∀ i, 0 ≤ p.coeff i)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    p.eval x ≤ p.eval y := by
  classical
  simp only [Polynomial.eval_eq_sum_range]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy i) (hp i)

lemma polynomial_eval_nonneg_of_coeff_nonneg
    {p : Polynomial ℝ} (hp : ∀ i, 0 ≤ p.coeff i) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ p.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hp i) (pow_nonneg hx i)

/-- Every iterated spatial derivative of the heat kernel is exactly a
polynomial times the original Gaussian exponential. -/
lemma heatKernel_iterate_deriv_eq_polynomial_gaussian
    {t : ℝ} (_ht : 0 < t) (n : ℕ) (x : ℝ) :
    deriv^[n] (heatKernel t) x =
      (heatKernelDerivPoly t n).eval x * Real.exp (-x ^ 2 / (4 * t)) := by
  induction n generalizing x with
  | zero =>
      simp [heatKernelDerivPoly, heatKernel]
  | succ n ih =>
      have ihfun : deriv^[n] (heatKernel t) = fun x =>
          (heatKernelDerivPoly t n).eval x * Real.exp (-x ^ 2 / (4 * t)) :=
        funext ih
      rw [Function.iterate_succ_apply', ihfun]
      have harg : HasDerivAt (fun y : ℝ => -y ^ 2 / (4 * t))
          (-(2 * x) / (4 * t)) x := by
        convert (((hasDerivAt_id x).pow 2).neg.div_const (4 * t)) using 1
        all_goals norm_num
      rw [deriv_fun_mul]
      · rw [Polynomial.deriv, harg.exp.deriv]
        simp only [heatKernelDerivPoly, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X]
        ring
      · exact (heatKernelDerivPoly t n).differentiableAt
      · exact harg.exp.differentiableAt

/-- Every heat-kernel derivative admits a coefficientwise-nonnegative
polynomial majorant. -/
lemma heatKernel_iterate_deriv_polynomial_bound
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∃ P : Polynomial ℝ, (∀ i, 0 ≤ P.coeff i) ∧
      ∀ u, |deriv^[n] (heatKernel t) u| ≤
        P.eval |u| * Real.exp (-u ^ 2 / (4 * t)) := by
  let p := heatKernelDerivPoly t n
  refine ⟨polynomialAbsCoeff p, polynomialAbsCoeff_coeff_nonneg p, ?_⟩
  intro u
  rw [heatKernel_iterate_deriv_eq_polynomial_gaussian ht]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right
    (abs_polynomial_eval_le_absCoeff p u) (Real.exp_pos _).le

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

/-- A polynomial in `|x| + 1`, multiplied by a Gaussian, is in `L²`.
Splitting at zero turns the absolute value into two ordinary polynomials. -/
lemma memLp_two_polynomial_abs_add_one_gaussian
    (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :
    MemLp (fun x : ℝ => p.eval (|x| + 1) * Real.exp (-b * x ^ 2)) 2 volume := by
  let qpos := (p.comp (Polynomial.X + Polynomial.C 1)) ^ 2
  let qneg := (p.comp (-Polynomial.X + Polynomial.C 1)) ^ 2
  have hpos := integrable_polynomial_mul_exp_neg_mul_sq qpos
    (show 0 < 2 * b by positivity)
  have hneg := integrable_polynomial_mul_exp_neg_mul_sq qneg
    (show 0 < 2 * b by positivity)
  have hpiece : Integrable ((Set.Ici (0 : ℝ)).piecewise
      (fun x => qpos.eval x * Real.exp (-(2 * b) * x ^ 2))
      (fun x => qneg.eval x * Real.exp (-(2 * b) * x ^ 2))) volume :=
    Integrable.piecewise measurableSet_Ici hpos.integrableOn hneg.integrableOn
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => p.eval (|x| + 1) * Real.exp (-b * x ^ 2)) volume := by
    fun_prop
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  apply hpiece.congr
  filter_upwards with x
  by_cases hx : 0 ≤ x
  · simp only [Set.piecewise, Set.mem_Ici, hx, ↓reduceIte, abs_of_nonneg hx,
      qpos, Polynomial.eval_pow, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [mul_pow]
    congr 1
    simp only [pow_two]
    rw [← Real.exp_add]
    congr 1
    ring
  · have hx' : x < 0 := lt_of_not_ge hx
    simp only [Set.piecewise, Set.mem_Ici, hx, ↓reduceIte, abs_of_neg hx',
      qneg, Polynomial.eval_pow, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_C]
    rw [mul_pow]
    congr 1
    simp only [pow_two]
    rw [← Real.exp_add]
    congr 1
    ring

/-- Every iterated spatial derivative of a positive-time heat kernel is in
`L²`; its square is again a polynomial times a decaying Gaussian. -/
lemma heatKernel_iterate_deriv_memLp_two
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    MemLp (deriv^[n] (heatKernel t)) 2 volume := by
  have hmeas : AEStronglyMeasurable (deriv^[n] (heatKernel t)) volume :=
    ((heatKernel_contDiff ht).iterate_deriv n).continuous.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  let p := heatKernelDerivPoly t n
  have h := integrable_polynomial_mul_exp_neg_mul_sq (p * p)
    (show 0 < 1 / (2 * t) by positivity)
  apply h.congr
  filter_upwards with x
  rw [heatKernel_iterate_deriv_eq_polynomial_gaussian ht]
  simp only [Polynomial.eval_mul, mul_pow]
  rw [show Real.exp (-x ^ 2 / (4 * t)) ^ 2 =
      Real.exp (-(1 / (2 * t)) * x ^ 2) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  ring

/-- On a unit ball in the convolution parameter, the `n`th differentiated
integrand has a single integrable polynomial--Gaussian envelope. -/
lemma heatKernel_iterate_deriv_local_envelope
    {t : ℝ} (ht : 0 < t) (n : ℕ) (x₀ : ℝ)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      ∀ y, ∀ x ∈ Metric.ball x₀ 1,
        ‖(deriv^[n] (heatKernel t)) (x - y) * f y‖ ≤ bound y := by
  obtain ⟨p, hp, hp_bound⟩ := heatKernel_iterate_deriv_polynomial_bound ht n
  let a : ℝ → ℝ := fun v =>
    p.eval (|v| + 1) * Real.exp (-(1 / (8 * t)) * v ^ 2)
  have ha : MemLp a 2 volume :=
    memLp_two_polynomial_abs_add_one_gaussian p
      (show 0 < 1 / (8 * t) by positivity)
  have hashift : MemLp (fun y => a (x₀ - y)) 2 volume := by
    simpa only [Function.comp_apply] using
      ha.comp_measurePreserving (volume.measurePreserving_sub_left x₀)
  have hfabs : MemLp (fun y => |f y|) 2 volume := by
    simpa only [Real.norm_eq_abs] using hf.norm
  let c := Real.exp (1 / (2 * t))
  refine ⟨fun y => c * (a (x₀ - y) * |f y|),
    (hashift.integrable_mul hfabs).const_mul c, ?_⟩
  intro y x hx
  let u := x - y
  let v := x₀ - y
  have hd : |x - x₀| < 1 := by
    simpa only [Real.dist_eq] using hx
  have huv : u = v + (x - x₀) := by simp only [u, v]; ring
  have habs : |u| ≤ |v| + 1 := by
    rw [huv]
    exact (abs_add_le _ _).trans (add_le_add_right hd.le |v|)
  have hpmono : p.eval |u| ≤ p.eval (|v| + 1) :=
    polynomial_eval_mono_of_coeff_nonneg hp (abs_nonneg u) habs
  have hpv : 0 ≤ p.eval (|v| + 1) :=
    polynomial_eval_nonneg_of_coeff_nonneg hp (by positivity)
  have hd_sq : (x - x₀) ^ 2 < 1 := by
    nlinarith [sq_abs (x - x₀), abs_nonneg (x - x₀)]
  have hquad : v ^ 2 / 2 - 2 ≤ u ^ 2 := by
    rw [huv]
    nlinarith [sq_nonneg (2 * v + (x - x₀))]
  have hexp : Real.exp (-u ^ 2 / (4 * t)) ≤
      c * Real.exp (-(1 / (8 * t)) * v ^ 2) := by
    rw [show c * Real.exp (-(1 / (8 * t)) * v ^ 2) =
        Real.exp (1 / (2 * t) + -(1 / (8 * t)) * v ^ 2) by
      simp only [c, ← Real.exp_add]]
    apply Real.exp_le_exp.mpr
    have ht0 : 0 < 8 * t := by positivity
    field_simp
    nlinarith
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |(deriv^[n] (heatKernel t)) u| * |f y| ≤
        (p.eval |u| * Real.exp (-u ^ 2 / (4 * t))) * |f y| :=
      mul_le_mul_of_nonneg_right (hp_bound u) (abs_nonneg _)
    _ ≤ (p.eval (|v| + 1) * Real.exp (-u ^ 2 / (4 * t))) * |f y| := by
      gcongr
    _ ≤ (p.eval (|v| + 1) *
          (c * Real.exp (-(1 / (8 * t)) * v ^ 2))) * |f y| := by
      gcongr
    _ = c * (a (x₀ - y) * |f y|) := by
      simp only [a, v]
      ring

/-- Differentiation under the integral for every iterated heat-kernel
derivative. -/
lemma hasDerivAt_integral_iterate_heatKernel
    {t : ℝ} (ht : 0 < t) (n : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (x₀ : ℝ) :
    HasDerivAt
      (fun x => ∫ y, (deriv^[n] (heatKernel t)) (x - y) * f y ∂volume)
      (∫ y, (deriv^[n + 1] (heatKernel t)) (x₀ - y) * f y ∂volume) x₀ := by
  let F : ℝ → ℝ → ℝ := fun x y =>
    (deriv^[n] (heatKernel t)) (x - y) * f y
  let F' : ℝ → ℝ → ℝ := fun x y =>
    (deriv^[n + 1] (heatKernel t)) (x - y) * f y
  obtain ⟨bound, hbound_int, hbound⟩ :=
    heatKernel_iterate_deriv_local_envelope ht (n + 1) x₀ hf
  have hDn_cont : Continuous (deriv^[n] (heatKernel t)) :=
    ((heatKernel_contDiff ht).iterate_deriv n).continuous
  have hDsn_cont : Continuous (deriv^[n + 1] (heatKernel t)) :=
    ((heatKernel_contDiff ht).iterate_deriv (n + 1)).continuous
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) volume := by
    filter_upwards with x
    exact (hDn_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hf.1
  have hF_int : Integrable (F x₀) volume := by
    have hs : MemLp (fun y => (deriv^[n] (heatKernel t)) (x₀ - y)) 2 volume := by
      simpa only [Function.comp_apply] using
        (heatKernel_iterate_deriv_memLp_two ht n).comp_measurePreserving
          (volume.measurePreserving_sub_left x₀)
    exact hs.integrable_mul hf
  have hF'_meas : AEStronglyMeasurable (F' x₀) volume :=
    (hDsn_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.1
  have hdiff : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball x₀ 1,
      HasDerivAt (F · y) (F' x y) x := by
    filter_upwards with y
    intro x hx
    have hbase : HasDerivAt (deriv^[n] (heatKernel t))
        ((deriv^[n + 1] (heatKernel t)) (x - y)) (x - y) := by
      have hd := ((heatKernel_contDiff ht).iterate_deriv n).differentiable
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      convert (hd.differentiableAt.hasDerivAt (x := x - y)) using 1
      rw [Function.iterate_succ_apply']
    convert (hbase.comp x ((hasDerivAt_id x).sub_const y)).mul_const (f y) using 1
    all_goals simp only [F', mul_one]
  have hbound' : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball x₀ 1,
      ‖F' x y‖ ≤ bound y := by
    filter_upwards with y
    exact hbound y
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x₀ zero_lt_one) hF_meas hF_int hF'_meas
    hbound' hbound_int hdiff).2

/-- The `n`th derivative of the heat convolution is convolution with the
`n`th derivative of the heat kernel. -/
lemma iterate_deriv_heatConv_eq_integral
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (n : ℕ) (x : ℝ) :
    (deriv^[n] (heatConv t f)) x =
      ∫ y, (deriv^[n] (heatKernel t)) (x - y) * f y ∂volume := by
  induction n generalizing x with
  | zero => simp [heatConv]
  | succ n ih =>
      have ihfun : deriv^[n] (heatConv t f) = fun x =>
          ∫ y, (deriv^[n] (heatKernel t)) (x - y) * f y ∂volume :=
        funext ih
      rw [Function.iterate_succ_apply', ihfun]
      simpa only [Nat.add_eq, Nat.succ_eq_add_one] using
        (hasDerivAt_integral_iterate_heatKernel ht n hf x).deriv

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

/-- Every iterated derivative of the standard Gaussian is square-integrable. -/
lemma memLp_two_iterate_deriv_standardGaussian (n : ℕ) :
    MemLp (deriv^[n] (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (deriv^[n] (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))) volume :=
    ((show ContDiff ℝ ∞ (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) by
      fun_prop).iterate_deriv n).continuous.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  let p : Polynomial ℝ :=
    (Polynomial.hermite n).map (Int.castRingHom ℝ)
  have h := integrable_polynomial_mul_exp_neg_mul_sq (p * p)
    (show (0 : ℝ) < 1 by norm_num)
  apply h.congr
  filter_upwards with x
  rw [Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
  simp only [Polynomial.eval_mul]
  rw [show p.eval x = Polynomial.aeval x (Polynomial.hermite n) by
    exact Polynomial.eval_map (p := Polynomial.hermite n)
      (f := Int.castRingHom ℝ) x]
  rw [show -(1 : ℝ) * x ^ 2 = -(x ^ 2 / 2) + -(x ^ 2 / 2) by ring,
    Real.exp_add]
  ring_nf
  rw [show (-1 : ℝ) ^ (n * 2) = 1 by
    rw [show n * 2 = 2 * n by omega, pow_mul]
    norm_num]
  ring

/-- The first derivative of a positive-time heat kernel is square-integrable. -/
lemma heatKernel_deriv_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp (fun x => -(x / (2 * t)) * heatKernel t x) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun x => -(x / (2 * t)) * heatKernel t x) volume := by
    unfold heatKernel
    fun_prop
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have hgauss := integrable_pow_mul_exp_neg_mul_sq 2
    (show (0 : ℝ) < 1 / (2 * t) by positivity)
  have h := hgauss.const_mul
    (((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ 2 / (4 * t ^ 2))
  apply h.congr
  filter_upwards with x
  unfold heatKernel
  have hexp :
      Real.exp (-x ^ 2 / (4 * t)) ^ 2 =
        Real.exp (-(1 / (2 * t)) * x ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [mul_pow]
  rw [hexp]
  ring

/-- At each spatial point, the first differentiated convolution integrand is
integrable by Cauchy--Schwarz. -/
lemma heatKernel_deriv_mul_integrable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (x : ℝ) :
    Integrable
      (fun y => (-((x - y) / (2 * t)) * heatKernel t (x - y)) * f y)
      volume := by
  have hshift : MemLp
      (fun y : ℝ => -((x - y) / (2 * t)) * heatKernel t (x - y))
      2 volume :=
    (heatKernel_deriv_memLp_two ht).comp_measurePreserving
      (volume.measurePreserving_sub_left x)
  exact hshift.integrable_mul hf

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
  let H : ℕ → ℝ → ℝ := fun n x =>
    ∫ y, (deriv^[n] (heatKernel t)) (x - y) * f y ∂volume
  have hdiff : ∀ n, Differentiable ℝ (H n) := by
    intro n x
    exact (by
      simpa only [H] using
        (hasDerivAt_integral_iterate_heatKernel ht n hf x).differentiableAt)
  have hderiv : ∀ n, deriv (H n) = H (n + 1) := by
    intro n
    funext x
    exact (by
      simpa only [H] using
        (hasDerivAt_integral_iterate_heatKernel ht n hf x).deriv)
  have hcont : ∀ m n : ℕ, ContDiff ℝ m (H n) := by
    intro m
    induction m with
    | zero =>
        intro n
        exact contDiff_zero.mpr (hdiff n).continuous
    | succ m ih =>
        intro n
        rw [show (↑(m + 1) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_num,
          contDiff_succ_iff_deriv]
        refine ⟨hdiff n, ?_, ?_⟩
        · simp
        · rw [hderiv n]
          exact ih (n + 1)
  rw [contDiff_iff_forall_nat_le]
  intro m hm
  have hmH := hcont m 0
  simpa only [H, Function.iterate_zero_apply, heatConv] using hmH

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
