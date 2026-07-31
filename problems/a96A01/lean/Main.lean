/-
! # APM a96A01: Lp quasi-norms for 0 < p ≤ 1, monotonicity, and geometric mean limit

(a) ‖f‖_p ≤ ‖f‖_q when 0 < p < q ≤ 1 (antitone in p), so L = lim_{p→0⁺} ‖f‖_p exists.
(b) L > 0 implies |f| > 0 a.e.
(c) L ≥ exp(∫ log|f|).

## Proof strategy

(a) Hölder on |f|^p · 1 with exponents q/p and its conjugate.
(b) t^p ≤ 1+t gives dominated convergence: ∫|f|^p → m({f≠0}).
(c) Jensen for convex exp: ∫e^{p log|f|} ≥ e^{p ∫log|f|}.

## Theory boundaries

- Hölder's inequality IS in Mathlib but needs adaptation for 0 < p < 1.
- Jensen for integrals (ConvexOn) IS in Mathlib.
- The dominated convergence theorem IS in Mathlib.
- The limit computation p → 0 requires filter-based arguments.
- The hint t^p ≤ 1+t is a tractable calculus lemma.

## Statement repair

Used Mathlib's `MemLp` (not `Memℒp`). The `quasiNorm` uses interval integral
on [0,1]. Variable `μ` changed to `volume.restrict (Icc 0 1)` directly.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Set Filter Real Topology

open scoped ENNReal

noncomputable section

/-- The Lp quasi-norm for 0 < p: (∫₀¹ |f|^p)^{1/p}. -/
def quasiNorm (f : ℝ → ℝ) (p : ℝ) : ℝ :=
  (∫ x in Set.Icc (0:ℝ) 1, ‖f x‖ ^ p ∂volume) ^ (1 / p)

/-- The hint: t^p ≤ 1 + t for t ≥ 0 and 0 < p ≤ 1.

This follows from the concavity of x ↦ x^p for 0 < p < 1:
x^p is concave with x^p(0) = 0, x^p(1) = 1, so x^p ≤ (1-0)·1 + 0 = 1
for x ∈ [0,1]. For x ≥ 1: x^p ≤ x (since p ≤ 1).
So x^p ≤ max(1, x) ≤ 1 + x for all x ≥ 0. -/
lemma rpow_le_one_add {t : ℝ} (ht : 0 ≤ t) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    t ^ p ≤ 1 + t := by
  by_cases h1 : t ≤ 1
  · -- For t ∈ [0,1]: t^p ≤ 1 since p > 0 and 0 ≤ t ≤ 1.
    have : t ^ p ≤ 1 := Real.rpow_le_one ht h1 hp.le
    linarith
  · -- For t > 1: t^p ≤ t^1 = t since p ≤ 1 and t ≥ 1.
    have htt : t ^ (1 : ℝ) = t := rpow_one t
    have : t ^ p ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hp1
    rw [htt] at this
    linarith

/-- On the unit interval, `quasiNorm` is Mathlib's real-valued `Lᵖ`
seminorm. -/
lemma quasiNorm_eq_lpNorm
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume)
    {p : ℝ} (hp : 0 < p) :
    quasiNorm f p =
      lpNorm f (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) := by
  have hmeas : AEStronglyMeasurable f (volume.restrict (Icc 0 1)) :=
    hf.aestronglyMeasurable
  rw [quasiNorm,
    lpNorm_eq_integral_norm_rpow_toReal
      (by positivity)
      (by simp) hmeas]
  simp [ENNReal.toReal_ofReal hp.le]

/-- (a) ‖f‖_p ≤ ‖f‖_q when 0 < p < q ≤ 1.

This is the probability-space exponent comparison for `Lᵖ` seminorms,
transported through `quasiNorm_eq_lpNorm`. -/
theorem quasiNorm_antitone
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    quasiNorm f p ≤ quasiNorm f q := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by
    simp [μ, Real.volume_Icc]⟩
  have hmeas : AEStronglyMeasurable f μ := by
    simpa [μ] using hf.aestronglyMeasurable
  have hq0 : 0 < q := hp.trans hpq
  have hpq' : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal hpq.le
  have hq_mem : MemLp f (ENNReal.ofReal q) μ := by
    have hf_one : MemLp f 1 μ := by
      rw [memLp_one_iff_integrable]
      simpa [μ] using hf
    exact hf_one.mono_exponent (by
      simpa using ENNReal.ofReal_le_ofReal hq)
  rw [quasiNorm_eq_lpNorm hf hp, quasiNorm_eq_lpNorm hf hq0,
    ← toReal_eLpNorm hmeas, ← toReal_eLpNorm hmeas]
  exact ENNReal.toReal_mono hq_mem.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq' hmeas)

/-- The limit L = lim_{p→0⁺} ‖f‖_p exists.

Since `p ↦ ‖f‖_p` is monotone on `(0,1)` and bounded below by zero,
the order-topology right-limit theorem applies. -/
theorem quasiNorm_tendsto_exists
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume) :
    ∃ L : ℝ, Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have hmono : MonotoneOn (quasiNorm f) (Ioo (0 : ℝ) 1) := by
    intro p hp' q hq' hpq'
    rcases hpq'.eq_or_lt with rfl | hpq'
    · exact le_rfl
    · exact quasiNorm_antitone hf hp'.1 hpq' hq'.2.le
  have hbdd : BddBelow (quasiNorm f '' Ioo (0 : ℝ) 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, hp', rfl⟩
    apply Real.rpow_nonneg
    exact integral_nonneg_of_ae
      (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact ⟨sInf (quasiNorm f '' Ioo (0 : ℝ) 1),
    MonotoneOn.tendsto_nhdsWithin_Ioo_right
      ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ hmono hbdd⟩

/-- As `p → 0⁺`, the integral defining `quasiNorm f p` tends to the
measure of the essential support of `f`. -/
lemma integral_norm_rpow_tendsto_measure_support
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) :
    Tendsto (fun p : ℝ => ∫ x in Icc (0 : ℝ) 1, ‖f x‖ ^ p ∂volume)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((volume.restrict (Icc 0 1)) {x | 0 < ‖f x‖}).toReal) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let s : Set ℝ := {x | 0 < ‖f x‖}
  have hfm : AEStronglyMeasurable f μ := by
    simpa [μ] using hf.aestronglyMeasurable
  have hsm : NullMeasurableSet s μ := by
    exact hfm.norm.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
  have hbound : Integrable (fun x => 1 + ‖f x‖) μ := by
    simpa [μ] using (integrable_const (μ := μ) (1 : ℝ)).add hf.norm
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun p : ℝ => ‖f x‖ ^ p) (nhdsWithin 0 (Ioi 0))
        (nhds (s.indicator (fun _ => (1 : ℝ)) x)) := by
    filter_upwards [] with x
    by_cases hx : 0 < ‖f x‖
    · simp only [s, Set.mem_setOf_eq, hx, indicator_of_mem]
      simpa using
        (Real.continuousAt_const_rpow (a := ‖f x‖) (b := 0) (ne_of_gt hx)).tendsto.mono_left
          inf_le_left
    · have hx0 : ‖f x‖ = 0 := le_antisymm (not_lt.mp hx) (norm_nonneg _)
      have hev : ∀ᶠ p : ℝ in nhdsWithin 0 (Ioi 0), ‖f x‖ ^ p = 0 := by
        filter_upwards [self_mem_nhdsWithin] with p hp
        rw [hx0, Real.zero_rpow (ne_of_gt hp)]
      have hxmem : x ∉ s := by simpa [s] using hx
      rw [Set.indicator_of_notMem hxmem]
      exact (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin 0 (Ioi 0)) (nhds 0)).congr'
          (Filter.EventuallyEq.symm hev)
  have hp_one : ∀ᶠ p : ℝ in nhdsWithin 0 (Ioi 0), p ≤ 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with p hp _
    exact hp.le
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun x => 1 + ‖f x‖)
    (by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable hfm.norm)
    (by
      filter_upwards [self_mem_nhdsWithin, hp_one] with p hp hp1
      exact ae_of_all μ fun x => by
        calc
          ‖‖f x‖ ^ p‖ = ‖f x‖ ^ p :=
            Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)
          _ ≤ 1 + ‖f x‖ := rpow_le_one_add (norm_nonneg _) hp hp1)
    hbound hlim
  have hsint : ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ = (μ s).toReal := by
    rw [integral_indicator₀ hsm, setIntegral_one_eq_measureReal]
    rfl
  rw [hsint] at ht
  simpa [μ, s] using ht

/-- (b) L > 0 implies |f| > 0 a.e.

DCT gives `∫ |f|^p → volume {x | f x ≠ 0}`. If the zero set has positive
measure, the latter is strictly below one, and raising an eventual bound
`< 1` to `1 / p → ∞` forces `quasiNorm f p → 0`, contradicting `L > 0`. -/
theorem ae_pos_of_limit_pos
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    {L : ℝ} (hL : 0 < L)
    (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖ := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let s : Set ℝ := {x | 0 < ‖f x‖}
  have hfm : AEStronglyMeasurable f μ := by
    simpa [μ] using hf.aestronglyMeasurable
  have hsm : NullMeasurableSet s μ :=
    hfm.norm.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
  by_contra hpos
  have hμs_ne : μ s ≠ μ univ := by
    intro hμs
    apply hpos
    simpa [μ, s] using (ae_iff_measure_eq hsm).2 hμs
  have hμuniv : μ univ = 1 := by simp [μ, Real.volume_Icc]
  have hμs_lt : μ s < 1 := by
    rw [← hμuniv]
    exact lt_of_le_of_ne (measure_mono (subset_univ s)) hμs_ne
  have hc_lt : (μ s).toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal (measure_ne_top μ s) ENNReal.one_ne_top).2 hμs_lt
    simpa using this
  let r : ℝ := ((μ s).toReal + 1) / 2
  have hcr : (μ s).toReal < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hr0 : 0 < r := by
    dsimp [r]
    have := (ENNReal.toReal_nonneg : 0 ≤ (μ s).toReal)
    linarith
  have hint := integral_norm_rpow_tendsto_measure_support hf
  have hint' : Tendsto
      (fun p : ℝ => ∫ x, ‖f x‖ ^ p ∂μ)
      (nhdsWithin 0 (Ioi 0)) (nhds ((μ s).toReal)) := by
    simpa [μ, s] using hint
  have hint_lt : ∀ᶠ p : ℝ in nhdsWithin 0 (Ioi 0),
      (∫ x, ‖f x‖ ^ p ∂μ) ≤ r :=
    ((tendsto_order.1 hint').2 r hcr).mono fun _ hp => hp.le
  have hrpow : Tendsto (fun p : ℝ => r ^ (1 / p))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [one_div, Function.comp_apply] using
      (tendsto_rpow_atTop_of_base_lt_one r (by linarith) hr1).comp
        (tendsto_inv_nhdsGT_zero :
          Tendsto (fun p : ℝ => p⁻¹) (nhdsWithin 0 (Ioi 0)) atTop)
  have hq_nonneg : ∀ᶠ p : ℝ in nhdsWithin 0 (Ioi 0), 0 ≤ quasiNorm f p := by
    filter_upwards [] with p
    exact Real.rpow_nonneg
      (integral_nonneg_of_ae (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) p)) _
  have hq_le : ∀ᶠ p : ℝ in nhdsWithin 0 (Ioi 0), quasiNorm f p ≤ r ^ (1 / p) := by
    filter_upwards [self_mem_nhdsWithin, hint_lt] with p hp hpr
    rw [quasiNorm]
    apply Real.rpow_le_rpow
    · exact integral_nonneg_of_ae
        (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) p)
    · simpa [μ] using hpr
    · exact one_div_nonneg.mpr hp.le
  have hzero : Tendsto (quasiNorm f) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrpow hq_nonneg hq_le
  have : L = 0 := tendsto_nhds_unique hLim hzero
  linarith

/-- Jensen's inequality at a fixed positive exponent, after the logarithm has
been shown integrable.  This packages the final step independently of the
one-sided Fatou argument needed to establish logarithmic integrability. -/
lemma geometric_mean_le_quasiNorm_of_integrable_log
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    (hf_pos : ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖)
    (hlog : IntegrableOn (fun x => log ‖f x‖) (Icc 0 1) volume)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    exp (∫ x in Icc (0 : ℝ) 1, log ‖f x‖ ∂volume) ≤ quasiNorm f p := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  have hfm : AEStronglyMeasurable f μ := by
    simpa [μ] using hf.aestronglyMeasurable
  have hpow_meas : AEStronglyMeasurable (fun x => ‖f x‖ ^ p) μ :=
    (Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable hfm.norm
  have hbound : Integrable (fun x => 1 + ‖f x‖) μ := by
    simpa [μ] using (integrable_const (μ := μ) (1 : ℝ)).add hf.norm
  have hpow_int : Integrable (fun x => ‖f x‖ ^ p) μ := by
    refine hbound.mono' hpow_meas ?_
    exact ae_of_all μ fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
      exact rpow_le_one_add (norm_nonneg _) hp hp1
  have hplog_int : Integrable (fun x => p * log ‖f x‖) μ := by
    simpa [μ] using hlog.const_mul p
  have hexp_int : Integrable (fun x => exp (p * log ‖f x‖)) μ := by
    refine hpow_int.congr ?_
    filter_upwards [hf_pos] with x hx
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hjensen :
      exp (∫ x, p * log ‖f x‖ ∂μ) ≤ ∫ x, exp (p * log ‖f x‖) ∂μ := by
    exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (ae_of_all μ fun _ => mem_univ _) hplog_int hexp_int
  have hjensen' :
      exp (p * ∫ x, log ‖f x‖ ∂μ) ≤ ∫ x, ‖f x‖ ^ p ∂μ := by
    rw [integral_const_mul] at hjensen
    refine hjensen.trans_eq (integral_congr_ae ?_)
    filter_upwards [hf_pos] with x hx
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hrpow := Real.rpow_le_rpow (Real.exp_nonneg _) hjensen' (one_div_nonneg.mpr hp.le)
  have hleft :
      exp (p * ∫ x, log ‖f x‖ ∂μ) ^ (1 / p) = exp (∫ x, log ‖f x‖ ∂μ) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    field_simp
  rw [hleft] at hrpow
  rw [quasiNorm]
  simpa [μ] using hrpow

/-- (c) L ≥ exp(∫ log|f|).

**Remaining construction:** derive integrability of the negative part of
`log ‖f‖` from `L > 0`. Its positive part is controlled by `f`; for the
negative part, apply a one-sided Fatou/uniform-integrability argument to
`p⁻¹ * (‖f‖ ^ p - 1)`, whose pointwise limit is `log ‖f‖`. Once this is
integrable, Jensen for `exp` gives the inequality at every positive exponent,
and `hLim` supplies the limit. -/
theorem limit_ge_geometric_mean
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    (hf_pos : ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖)
    {L : ℝ} (hL : 0 < L)
    (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    exp (∫ x in Set.Icc (0:ℝ) 1, log ‖f x‖ ∂volume) ≤ L := by
  by_cases hlog : IntegrableOn (fun x => log ‖f x‖) (Icc 0 1) volume
  · apply ge_of_tendsto hLim
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with p hp hp1
    exact geometric_mean_le_quasiNorm_of_integrable_log hf hf_pos hlog hp hp1
  · -- Remaining frontier: `hL > 0` rules out a nonintegrable negative
    -- logarithmic tail.  A one-sided Fatou argument applied to
    -- `p⁻¹ * (1 - ‖f‖^p)` supplies this implication.
    sorry

end
