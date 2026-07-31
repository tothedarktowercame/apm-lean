import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.MeanInequalitiesPow

open MeasureTheory Set ENNReal Filter Topology

noncomputable section

/-! # APM a02J02: Radon-Riesz theorem for Lp (1 < p < ∞)

  f_n → f a.e., ‖f_n‖_p → ‖f‖_p  ⟹  f_n → f in Lp.

  NOT in Mathlib as of 2026-03. The proof applies Scheffé's lemma to
  `|f_n|^p`, transfers uniform integrability back to `f_n`, and concludes
  with Vitali convergence on the finite-measure interval.
-/

-- CLOSED: (s+t)^p ≤ 2^p (s^p + t^p) for s,t ≥ 0, nat p
lemma add_pow_le_two_pow_mul {p : ℕ} (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s + t) ^ p ≤ 2 ^ p * (s ^ p + t ^ p) := by
  have hst : s + t ≤ 2 * max s t := by
    calc s + t ≤ max s t + max s t := add_le_add (le_max_left s t) (le_max_right s t)
      _ = 2 * max s t := by ring
  have hmax : max s t ^ p ≤ s ^ p + t ^ p := by
    rcases le_total s t with h | h
    · simp [max_eq_right h]; linarith [pow_nonneg hs p]
    · simp [max_eq_left h]; linarith [pow_nonneg ht p]
  calc (s + t) ^ p
      ≤ (2 * max s t) ^ p := by gcongr
    _ = 2 ^ p * max s t ^ p := by rw [mul_pow]
    _ ≤ 2 ^ p * (s ^ p + t ^ p) := by gcongr

-- CLOSED: |a-b|^p ≤ 2^p (|a|^p + |b|^p) for nat p
lemma abs_sub_pow_le {p : ℕ} (a b : ℝ) :
    |a - b| ^ p ≤ 2 ^ p * (|a| ^ p + |b| ^ p) :=
  calc |a - b| ^ p
      ≤ (|a| + |b|) ^ p := by
        gcongr; exact norm_sub_le a b
    _ ≤ 2 ^ p * (|a| ^ p + |b| ^ p) :=
        add_pow_le_two_pow_mul |a| |b| (abs_nonneg a) (abs_nonneg b)

-- CLOSED: real-exponent version via the generalized mean inequality
lemma rpow_sub_le {p : ℝ} (hp : 1 ≤ p) (a b : ℝ) :
    |a - b| ^ p ≤ 2 ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  calc
    |a - b| ^ p ≤ (|a| + |b|) ^ p := by
      exact Real.rpow_le_rpow (abs_nonneg _) (abs_sub a b) (zero_le_one.trans hp)
    _ ≤ 2 ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
        ⟨|a|, abs_nonneg a⟩ ⟨|b|, abs_nonneg b⟩ hp

/-- Scheffé's lemma for nonnegative real-valued functions, in the form needed
for the Radon--Riesz argument below. -/
lemma tendsto_integral_abs_sub_of_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : ℕ → α → ℝ} {v : α → ℝ}
    (hu_int : ∀ n, Integrable (u n) μ) (hv_int : Integrable v μ)
    (hu_nonneg : ∀ n, 0 ≤ᵐ[μ] u n) (hv_nonneg : 0 ≤ᵐ[μ] v)
    (huv : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds (v x)))
    (hint : Tendsto (fun n => ∫ x, u n x ∂μ) atTop (nhds (∫ x, v x ∂μ))) :
    Tendsto (fun n => ∫ x, |u n x - v x| ∂μ) atTop (nhds 0) := by
  have hmin_meas (n : ℕ) :
      AEStronglyMeasurable (fun x => min (u n x) (v x)) μ :=
    (hu_int n).aestronglyMeasurable.inf hv_int.aestronglyMeasurable
  have hmin_bound (n : ℕ) :
      ∀ᵐ x ∂μ, ‖min (u n x) (v x)‖ ≤ v x := by
    filter_upwards [hu_nonneg n, hv_nonneg] with x hux hvx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hux hvx)]
    exact min_le_right _ _
  have hmin_int (n : ℕ) : Integrable (fun x => min (u n x) (v x)) μ :=
    hv_int.mono (hmin_meas n) <| by
      filter_upwards [hmin_bound n, hv_nonneg] with x hbound hvx
      simpa [Real.norm_eq_abs, abs_of_nonneg hvx] using hbound
  have hmin_lim :
      ∀ᵐ x ∂μ, Tendsto (fun n => min (u n x) (v x)) atTop (nhds (v x)) := by
    filter_upwards [huv] with x hx
    have hc : Tendsto (fun _ : ℕ => v x) atTop (nhds (v x)) :=
      tendsto_const_nhds
    simpa using hx.min hc
  have hmin_integral :
      Tendsto (fun n => ∫ x, min (u n x) (v x) ∂μ) atTop
        (nhds (∫ x, v x ∂μ)) :=
    tendsto_integral_of_dominated_convergence v hmin_meas hv_int hmin_bound hmin_lim
  have habs_integral (n : ℕ) :
      (∫ x, |u n x - v x| ∂μ) =
        (∫ x, u n x ∂μ) + (∫ x, v x ∂μ) -
          2 * ∫ x, min (u n x) (v x) ∂μ := by
    have hfun :
        (fun x => |u n x - v x|) =
          fun x => u n x + v x - 2 * min (u n x) (v x) := by
      funext x
      rcases le_total (u n x) (v x) with hle | hle
      · rw [min_eq_left hle, abs_of_nonpos (sub_nonpos.2 hle)]
        ring
      · rw [min_eq_right hle, abs_of_nonneg (sub_nonneg.2 hle)]
        ring
    rw [hfun]
    change (∫ x, ((u n + v) - fun y => 2 * min (u n y) (v y)) x ∂μ) =
      (∫ x, u n x ∂μ) + (∫ x, v x ∂μ) -
        2 * ∫ x, min (u n x) (v x) ∂μ
    calc
      (∫ x, ((u n + v) - fun y => 2 * min (u n y) (v y)) x ∂μ) =
          (∫ x, (u n + v) x ∂μ) -
            ∫ x, 2 * min (u n x) (v x) ∂μ :=
        integral_sub ((hu_int n).add hv_int) ((hmin_int n).const_mul 2)
      _ = (∫ x, u n x ∂μ) + (∫ x, v x ∂μ) -
          2 * ∫ x, min (u n x) (v x) ∂μ := by
        have hadd :
            (∫ x, (u n + v) x ∂μ) =
              (∫ x, u n x ∂μ) + ∫ x, v x ∂μ := by
          simpa only [Pi.add_apply] using integral_add (hu_int n) hv_int
        have hmul :
            (∫ x, 2 * min (u n x) (v x) ∂μ) =
              2 * ∫ x, min (u n x) (v x) ∂μ :=
          integral_const_mul 2 (fun x => min (u n x) (v x))
        rw [hadd, hmul]
  rw [show (0 : ℝ) =
      (∫ x, v x ∂μ) + (∫ x, v x ∂μ) - 2 * ∫ x, v x ∂μ by ring]
  apply Tendsto.congr' (Eventually.of_forall fun n => (habs_integral n).symm)
  exact (hint.add tendsto_const_nhds).sub (hmin_integral.const_mul 2)

lemma integral_abs_rpow_eq_eLpNorm_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ} (hp : 0 < p) {h : α → ℝ}
    (hh : MemLp h (ENNReal.ofReal p) μ) :
    (∫ x, |h x| ^ p ∂μ) =
      (eLpNorm h (ENNReal.ofReal p) μ).toReal ^ p := by
  let q : NNReal := Real.toNNReal p
  have hq_pos : 0 < (q : ℝ) := by
    simpa [q, Real.coe_toNNReal p hp.le] using hp
  have hq_ne : q ≠ 0 := ne_of_gt (NNReal.coe_pos.mp hq_pos)
  have hq_coe : (q : ℝ) = p := by
    simp [q, Real.coe_toNNReal p hp.le]
  have hq_ennreal : (q : ℝ≥0∞) = ENNReal.ofReal p := by
    rw [← hq_coe]
    simp
  have hlin :
      eLpNorm h (q : ℝ≥0∞) μ ^ (q : ℝ) =
        ∫⁻ x, ‖h x‖ₑ ^ (q : ℝ) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral hq_ne
  have hmeas :
      AEMeasurable (fun x => ‖h x‖ₑ ^ (q : ℝ)) μ :=
    hh.aestronglyMeasurable.enorm.pow_const _
  have hfinite :
      ∀ᵐ x ∂μ, ‖h x‖ₑ ^ (q : ℝ) < ∞ := by
    exact .of_forall fun x =>
      ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)
  calc
    (∫ x, |h x| ^ p ∂μ) =
        ∫ x, (‖h x‖ₑ ^ (q : ℝ)).toReal ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hq_coe, enorm_eq_nnnorm, ← ENNReal.toReal_rpow]
      simp [Real.norm_eq_abs]
    _ = (∫⁻ x, ‖h x‖ₑ ^ (q : ℝ) ∂μ).toReal :=
      integral_toReal hmeas hfinite
    _ = (eLpNorm h (q : ℝ≥0∞) μ ^ (q : ℝ)).toReal := by rw [← hlin]
    _ = (eLpNorm h (ENNReal.ofReal p) μ).toReal ^ p := by
      rw [ENNReal.toReal_rpow, hq_ennreal, hq_coe]

lemma eLpNorm_indicator_rpow_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ} (hp : 0 < p) (s : Set α) (h : α → ℝ) :
    eLpNorm (s.indicator h) (ENNReal.ofReal p) μ ^ p =
      eLpNorm (s.indicator (fun x => |h x| ^ p)) 1 μ := by
  let q : NNReal := Real.toNNReal p
  have hq_ne : q ≠ 0 := by
    exact ne_of_gt <| by
      simpa [q, Real.coe_toNNReal p hp.le] using hp
  have hq_pos : 0 < q := pos_iff_ne_zero.mpr hq_ne
  have hq_coe : (q : ℝ) = p := by
    simp [q, Real.coe_toNNReal p hp.le]
  have hq_ennreal : (q : ℝ≥0∞) = ENNReal.ofReal p := by
    rw [← hq_coe]
    simp
  rw [← hq_ennreal, ← hq_coe, eLpNorm_nnreal_pow_eq_lintegral hq_ne,
    eLpNorm_one_eq_lintegral_enorm]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, enorm_eq_nnnorm]
    rw [← ENNReal.coe_rpow_of_nonneg ‖h x‖₊ (by positivity)]
    norm_cast
    apply NNReal.eq
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  · simp [hx, hq_pos]

-- Radon-Riesz theorem statement
theorem radon_riesz {p : ℝ} (hp1 : 1 < p)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict (Icc 0 1)))
    (hae : ∀ᵐ x ∂(volume.restrict (Icc 0 1)),
      Tendsto (fun n => f n x) atTop (nhds (g x)))
    (hnorm : Tendsto
      (fun n => eLpNorm (f n) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)))
      atTop (nhds (eLpNorm g (ENNReal.ofReal p) (volume.restrict (Icc 0 1))))) :
    Tendsto
      (fun n => eLpNorm (f n - g) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)))
      atTop (nhds 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 1)
  let q : ℝ≥0∞ := ENNReal.ofReal p
  let u : ℕ → ℝ → ℝ := fun n x => |f n x| ^ p
  let v : ℝ → ℝ := fun x => |g x| ^ p
  have hp0 : 0 < p := zero_lt_one.trans hp1
  have hq0 : q ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hqtop : q ≠ ⊤ := by simp [q]
  have hqreal : q.toReal = p := by
    exact ENNReal.toReal_ofReal hp0.le
  have hu_mem (n : ℕ) : MemLp (u n) 1 μ := by
    simpa only [u, q, hqreal, Real.norm_eq_abs] using
      (hf n).norm_rpow hq0 hqtop
  have hv_mem : MemLp v 1 μ := by
    simpa only [v, q, hqreal, Real.norm_eq_abs] using
      hg.norm_rpow hq0 hqtop
  have hu_int (n : ℕ) : Integrable (u n) μ :=
    memLp_one_iff_integrable.mp (hu_mem n)
  have hv_int : Integrable v μ :=
    memLp_one_iff_integrable.mp hv_mem
  have hu_nonneg (n : ℕ) : 0 ≤ᵐ[μ] u n :=
    .of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hv_nonneg : 0 ≤ᵐ[μ] v :=
    .of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _
  have huv : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds (v x)) := by
    filter_upwards [hae] with x hx
    exact (continuous_abs.continuousAt.rpow_const (Or.inr hp0.le)).tendsto.comp hx
  have hnorm_real :
      Tendsto (fun n => (eLpNorm (f n) q μ).toReal) atTop
        (nhds (eLpNorm g q μ).toReal) := by
    exact (ENNReal.tendsto_toReal hg.2.ne).comp (by simpa [q, μ] using hnorm)
  have hnorm_real_pow :
      Tendsto (fun n => (eLpNorm (f n) q μ).toReal ^ p) atTop
        (nhds ((eLpNorm g q μ).toReal ^ p)) := by
    exact (continuousAt_id.rpow_const (Or.inr hp0.le)).tendsto.comp hnorm_real
  have hint :
      Tendsto (fun n => ∫ x, u n x ∂μ) atTop (nhds (∫ x, v x ∂μ)) := by
    convert hnorm_real_pow using 1
    · funext n
      simpa only [u, q, μ] using
        integral_abs_rpow_eq_eLpNorm_rpow hp0 (hf n)
    · exact congrArg nhds <| by
        simpa only [v, q, μ] using
          integral_abs_rpow_eq_eLpNorm_rpow hp0 hg
  have hscheffe :
      Tendsto (fun n => ∫ x, |u n x - v x| ∂μ) atTop (nhds 0) :=
    tendsto_integral_abs_sub_of_nonneg hu_int hv_int hu_nonneg hv_nonneg huv hint
  have huv_mem (n : ℕ) : MemLp (u n - v) 1 μ :=
    (hu_mem n).sub hv_mem
  have huv_L1 :
      Tendsto (fun n => eLpNorm (u n - v) 1 μ) atTop (nhds 0) := by
    apply (ENNReal.tendsto_toReal_zero_iff (fun n => (huv_mem n).2.ne)).mp
    convert hscheffe using 1
    funext n
    rw [toReal_eLpNorm (huv_mem n).1, lpNorm_one_eq_integral_norm (huv_mem n).1]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hu_ui : UnifIntegrable u 1 μ :=
    unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top hu_mem hv_mem huv_L1
  have hf_ui : UnifIntegrable f q μ := by
    intro ε hε
    have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
    obtain ⟨δ, hδ, hsmall⟩ := hu_ui hεp
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    have hpow := hsmall n s hs hμs
    rw [← eLpNorm_indicator_rpow_eq hp0 s (f n)] at hpow
    rw [← ENNReal.ofReal_rpow_of_pos hε] at hpow
    exact (ENNReal.rpow_le_rpow_iff hp0).mp hpow
  have hq_one : 1 ≤ q := by
    change 1 ≤ ENNReal.ofReal p
    rw [ENNReal.one_le_ofReal]
    exact hp1.le
  exact tendsto_Lp_finite_of_tendsto_ae hq_one hqtop
    (fun n => (hf n).1) hg hf_ui (by simpa [μ] using hae)
