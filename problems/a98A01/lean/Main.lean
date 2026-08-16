import Mathlib

/-!
# APM a98A01

## Statement repairs

None.

## Encoding questions

None. The source's `ℝⁿ` is encoded as `EuclideanSpace ℝ (Fin n)` with
Lebesgue measure. Real powers `k^α` use `Real.rpow`. Uniform convergence is
uniform convergence of the functions on the whole Euclidean space; almost
everywhere convergence uses Lebesgue measure; and `L¹` convergence is stated
through the `eLpNorm` at exponent one, which also represents non-integrability
honestly by the value `⊤`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The dilation family `Fₖ(x) = k^α f(k|x|)` on the genuine space `ℝⁿ`. -/
def apm_a98a01_dilation {n : ℕ} (f : ℝ → ℝ) (α : ℝ)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.rpow (k : ℝ) α * f ((k : ℝ) * ‖x‖)

private lemma apm_a98a01_bounded_on_Ici (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Ici (0 : ℝ)))
    (hf_nonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t)
    (hf_infty : Tendsto (fun t : ℝ => t ^ 4 * f t) atTop (𝓝 1)) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → |f t| ≤ M := by
  have htail_ev : ∀ᶠ t : ℝ in atTop, t ^ 4 * f t < 2 :=
    (tendsto_order.1 hf_infty).2 2 (by norm_num)
  rw [eventually_atTop] at htail_ev
  obtain ⟨A₀, hA₀⟩ := htail_ev
  let A : ℝ := max 1 A₀
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA0 : A₀ ≤ A := le_max_right _ _
  have hcontIcc : ContinuousOn f (Icc 0 A) :=
    hf_cont.mono Icc_subset_Ici_self
  have hbdd : BddAbove (f '' Icc 0 A) :=
    isCompact_Icc.bddAbove_image hcontIcc
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max 2 C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro t ht
  rw [abs_of_nonneg (hf_nonneg t ht)]
  by_cases htA : t ≤ A
  · exact le_trans (hC ⟨t, ⟨ht, htA⟩, rfl⟩) (le_max_right _ _)
  · have hAt : A ≤ t := le_of_lt (lt_of_not_ge htA)
    have htail : t ^ 4 * f t < 2 := hA₀ t (hA0.trans hAt)
    have ht1 : 1 ≤ t := hA1.trans hAt
    have hpow : 1 ≤ t ^ 4 := one_le_pow₀ ht1
    have hf0 : 0 ≤ f t := hf_nonneg t ht
    have hft : f t ≤ t ^ 4 * f t := by nlinarith
    exact le_trans (le_trans hft htail.le) (le_max_left _ _)

private lemma apm_a98a01_factor_identity (f : ℝ → ℝ) (α r : ℝ)
    (k : ℕ) (hk : 0 < k) (hr : 0 < r) :
    Real.rpow (k : ℝ) α * f ((k : ℝ) * r) =
      (Real.rpow (k : ℝ) (α - 4) / r ^ 4) *
        ((((k : ℝ) * r) ^ 4) * f ((k : ℝ) * r)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkpow : Real.rpow (k : ℝ) α =
      Real.rpow (k : ℝ) (α - 4) * (k : ℝ) ^ 4 := by
    calc
      Real.rpow (k : ℝ) α = Real.rpow (k : ℝ) ((α - 4) + 4) := by norm_num
      _ = Real.rpow (k : ℝ) (α - 4) * Real.rpow (k : ℝ) 4 :=
        Real.rpow_add hkR _ _
      _ = Real.rpow (k : ℝ) (α - 4) * (k : ℝ) ^ 4 := by
        congr 1
        exact Real.rpow_natCast (k : ℝ) 4
  rw [hkpow, mul_pow]
  field_simp

private lemma apm_a98a01_recover_identity (f : ℝ → ℝ) (α r : ℝ)
    (k : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hG : (((k : ℝ) * r) ^ 4) * f ((k : ℝ) * r) ≠ 0) :
    Real.rpow (k : ℝ) (α - 4) =
      (r ^ 4 * (Real.rpow (k : ℝ) α * f ((k : ℝ) * r))) /
        ((((k : ℝ) * r) ^ 4) * f ((k : ℝ) * r)) := by
  have hfne : f ((k : ℝ) * r) ≠ 0 := by
    intro hf
    apply hG
    rw [hf, mul_zero]
  rw [apm_a98a01_factor_identity f α r k hk hr]
  field_simp [hfne]
  rw [mul_comm r (k : ℝ), mul_div_cancel_right₀ _ hfne]

private lemma apm_a98a01_ratio_f_eq (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) :
    ∀ᶠ t : ℝ in atTop,
      (t ^ (n - 1) * f t) / t ^ ((n : ℝ) - 5) = t ^ 4 * f t := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [div_eq_iff (Real.rpow_pos_of_pos ht _).ne']
  have hp : t ^ (n - 1) = t ^ 4 * t ^ ((n : ℝ) - 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  rw [hp]
  ring

private lemma apm_a98a01_radial_integrable_iff
    (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Ici (0 : ℝ)))
    (hf_infty : Tendsto (fun t : ℝ => t ^ 4 * f t) atTop (𝓝 1)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖) volume ↔ n ≤ 3 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [integrable_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  let g : ℝ → ℝ := fun t => t ^ (n - 1) * f t
  let p : ℝ → ℝ := fun t => t ^ ((n : ℝ) - 5)
  have hg_cont : ContinuousOn g (Ici 0) :=
    (continuous_pow (n - 1)).continuousOn.mul hf_cont
  have hp_cont : ContinuousOn p (Ioi 0) := by
    intro t ht
    exact (continuousAt_id.rpow_const (Or.inl ht.ne')).continuousWithinAt
  have hratio : Tendsto (fun t => g t / p t) atTop (𝓝 1) := by
    apply hf_infty.congr'
    simpa only [g, p] using
      (apm_a98a01_ratio_f_eq n hn f).mono (fun _ h => h.symm)
  have htheta : p =Θ[atTop] g :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio one_ne_zero
  constructor
  · intro hg
    have hg_top : IntegrableAtFilter g atTop :=
      ⟨Ioi 0, Ioi_mem_atTop 0, hg⟩
    have hp_sm : StronglyMeasurableAtFilter p atTop :=
      ⟨Ioi 0, Ioi_mem_atTop 0,
        hp_cont.aestronglyMeasurable measurableSet_Ioi⟩
    have hp_top : IntegrableAtFilter p atTop :=
      htheta.isBigO.integrableAtFilter hp_sm hg_top
    rw [integrableAtFilter_rpow_atTop_iff] at hp_top
    have hnlt : n < 4 := by
      exact_mod_cast (show (n : ℝ) < 4 by linarith)
    omega
  · intro hn3
    have hp_top : IntegrableAtFilter p atTop := by
      rw [integrableAtFilter_rpow_atTop_iff]
      change (n : ℝ) - 5 < -1
      have hcast : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
      linarith
    have hg_sm : StronglyMeasurableAtFilter g atTop :=
      ⟨Ioi 0, Ioi_mem_atTop 0,
        (hg_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi⟩
    have hg_top : IntegrableAtFilter g atTop :=
      htheta.symm.isBigO.integrableAtFilter hg_sm hp_top
    obtain ⟨a, ha⟩ := integrableAtFilter_atTop_iff.1 hg_top
    let b := max a 1
    have hab : Ici b ⊆ Ici a := Ici_subset_Ici.2 (le_max_left _ _)
    have htail : IntegrableOn g (Ici b) := ha.mono_set hab
    have hb0 : 0 ≤ b := le_trans zero_le_one (le_max_right _ _)
    have hlocal : IntegrableOn g (Icc 0 b) :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hg_cont.mono Icc_subset_Ici_self)
    have hall : IntegrableOn g (Ici 0) := by
      apply (hlocal.union htail).mono_set
      intro x hx
      by_cases hxb : x ≤ b
      · exact Or.inl ⟨hx, hxb⟩
      · exact Or.inr (le_of_lt (lt_of_not_ge hxb))
    exact hall.mono_set Ioi_subset_Ici_self

private lemma apm_a98a01_eLpNorm_comp_nat_smul
    (n : ℕ) (hn : 0 < n) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (k : ℕ) (hk : 0 < k) :
    eLpNorm (fun x => g ((k : ℝ) • x)) 1 volume =
      ENNReal.ofReal |(((k : ℝ) ^ n)⁻¹)| * eLpNorm g 1 volume := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => (k : ℝ) • x
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hemb : MeasurableEmbedding h :=
    (Homeomorph.smul (isUnit_iff_ne_zero.2 hkR).unit).measurableEmbedding
  calc
    eLpNorm (fun x => g ((k : ℝ) • x)) 1 volume =
        eLpNorm (g ∘ h) 1 volume := rfl
    _ = eLpNorm g 1 (Measure.map h volume) :=
      (hemb.eLpNorm_map_measure).symm
    _ = eLpNorm g 1 (ENNReal.ofReal |(((k : ℝ) ^ n)⁻¹)| • volume) := by
      rw [Measure.map_addHaar_smul volume hkR]
      simp only [finrank_euclideanSpace_fin, h]
    _ = ENNReal.ofReal |(((k : ℝ) ^ n)⁻¹)| * eLpNorm g 1 volume := by
      rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ∞)]
      simp

private lemma apm_a98a01_dilation_eLpNorm_eq
    (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) (α : ℝ)
    (k : ℕ) (hk : 0 < k) :
    eLpNorm (apm_a98a01_dilation (n := n) f α k) 1 volume =
      ENNReal.ofReal (Real.rpow (k : ℝ) (α - n)) *
        eLpNorm (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖) 1 volume := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f ‖x‖
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfun : apm_a98a01_dilation (n := n) f α k =
      Real.rpow (k : ℝ) α • (fun x => g ((k : ℝ) • x)) := by
    funext x
    simp only [apm_a98a01_dilation, Pi.smul_apply, smul_eq_mul, g, norm_smul,
      Real.norm_eq_abs, abs_of_pos hkR]
  rw [hfun, eLpNorm_const_smul,
    apm_a98a01_eLpNorm_comp_nat_smul n hn g k hk]
  simp only [Real.enorm_eq_ofReal_abs, g]
  have hamp : |Real.rpow (k : ℝ) α| = Real.rpow (k : ℝ) α :=
    abs_of_pos (Real.rpow_pos_of_pos hkR α)
  rw [hamp]
  have hinv : |(((k : ℝ) ^ n)⁻¹)| = Real.rpow (k : ℝ) (-(n : ℝ)) := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hkR n))]
    rw [← Real.rpow_natCast]
    exact (Real.rpow_neg hkR.le _).symm
  rw [hinv]
  rw [← mul_assoc,
    ← ENNReal.ofReal_mul (p := Real.rpow (k : ℝ) α)
      (q := Real.rpow (k : ℝ) (-(n : ℝ))) (Real.rpow_nonneg hkR.le α)]
  have hrpow : Real.rpow (k : ℝ) α * Real.rpow (k : ℝ) (-(n : ℝ)) =
      Real.rpow (k : ℝ) (α + -(n : ℝ)) :=
    (Real.rpow_add hkR α (-(n : ℝ))).symm
  rw [hrpow]
  congr 2

private lemma apm_a98a01_radial_eLpNorm_ne_zero
    (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Ici (0 : ℝ)))
    (hf_infty : Tendsto (fun t : ℝ => t ^ 4 * f t) atTop (𝓝 1)) :
    eLpNorm (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖) 1 volume ≠ 0 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f ‖x‖
  have hg_cont : Continuous g :=
    hf_cont.comp_continuous continuous_norm (fun x => norm_nonneg x)
  intro hzero
  have hzero_ae : g =ᵐ[volume] 0 :=
    (eLpNorm_eq_zero_iff hg_cont.aestronglyMeasurable one_ne_zero).mp hzero
  have hzero_all : g = 0 :=
    (hg_cont.ae_eq_iff_eq volume continuous_zero).mp hzero_ae
  have hpos_ev : ∀ᶠ t : ℝ in atTop, (1 / 2 : ℝ) < t ^ 4 * f t :=
    (tendsto_order.1 hf_infty).1 (1 / 2) (by norm_num)
  obtain ⟨t, hprod, ht⟩ :=
    (hpos_ev.and (eventually_gt_atTop (0 : ℝ))).exists
  have hft : 0 < f t :=
    pos_of_mul_pos_right (lt_trans (by norm_num) hprod) (by positivity : 0 ≤ t ^ 4)
  let i : Fin n := ⟨0, hn⟩
  let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i t
  have hxnorm : ‖x‖ = t := by simp [x, i, abs_of_pos ht]
  have hxzero := congr_fun hzero_all x
  simp only [g, Pi.zero_apply, hxnorm] at hxzero
  linarith

private lemma apm_a98a01_radial_eLpNorm_lt_top_iff
    (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Ici (0 : ℝ)))
    (hf_infty : Tendsto (fun t : ℝ => t ^ 4 * f t) atTop (𝓝 1)) :
    eLpNorm (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖) 1 volume < ∞ ↔
      n ≤ 3 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖) :=
    hf_cont.comp_continuous continuous_norm (fun x => norm_nonneg x)
  rw [← apm_a98a01_radial_integrable_iff n hn f hf_cont hf_infty]
  rw [← memLp_one_iff_integrable]
  simp only [MemLp, hc.aestronglyMeasurable, true_and]

theorem apm_a98a01 (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Ici (0 : ℝ)))
    (hf_nonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t)
    (hf_zero : Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 1))
    (hf_infty : Tendsto (fun t : ℝ => t ^ 4 * f t) atTop (𝓝 1))
    (α : ℝ) :
    (TendstoUniformly
        (fun k => apm_a98a01_dilation (n := n) f α k)
        (fun _ => 0) atTop ↔ α < 0) ∧
    ((∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Tendsto (fun k => apm_a98a01_dilation f α k x) atTop (𝓝 0)) ↔
      α < 4) ∧
    (Tendsto
        (fun k => eLpNorm (apm_a98a01_dilation (n := n) f α k) 1 volume)
        atTop (𝓝 0) ↔ n ≤ 3 ∧ α < n) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hu
      have hpos_ev : ∀ᶠ t : ℝ in atTop, (1 / 2 : ℝ) < t ^ 4 * f t :=
        (tendsto_order.1 hf_infty).1 (1 / 2) (by norm_num)
      have htpos_ev : ∀ᶠ t : ℝ in atTop, 0 < t := eventually_gt_atTop 0
      obtain ⟨t, hprod, ht⟩ := (hpos_ev.and htpos_ev).exists
      have hprod0 : 0 < t ^ 4 * f t := lt_trans (by norm_num) hprod
      have hft : 0 < f t := pos_of_mul_pos_right hprod0 (by positivity : 0 ≤ t ^ 4)
      by_contra hα
      have hα0 : 0 ≤ α := le_of_not_gt hα
      have hu' := (Metric.tendstoUniformly_iff.1 hu) (f t) hft
      obtain ⟨k, hk, hk1⟩ := (hu'.and (eventually_ge_atTop 1)).exists
      let i : Fin n := ⟨0, hn⟩
      let x : EuclideanSpace ℝ (Fin n) :=
        EuclideanSpace.single i (t / (k : ℝ))
      have hkpos : 0 < (k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
      have hnorm : ‖x‖ = t / (k : ℝ) := by
        simp [x, i, abs_of_pos ht]
      have harg : (k : ℝ) * ‖x‖ = t := by
        rw [hnorm]
        field_simp
      have hlt := hk x
      have hrpow0 : 0 ≤ Real.rpow (k : ℝ) α :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      simp only [apm_a98a01_dilation, harg, dist_zero_left, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hrpow0, abs_of_pos hft] at hlt
      have hkpow : 1 ≤ Real.rpow (k : ℝ) α :=
        Real.one_le_rpow (by exact_mod_cast hk1) hα0
      nlinarith
    · intro hα
      obtain ⟨M, hM, hbound⟩ :=
        apm_a98a01_bounded_on_Ici f hf_cont hf_nonneg hf_infty
      have hkpow : Tendsto (fun k : ℕ => Real.rpow (k : ℝ) α) atTop (𝓝 0) := by
        simpa only [Function.comp_apply, neg_neg] using
          (tendsto_rpow_neg_atTop (neg_pos.mpr hα)).comp
            (tendsto_natCast_atTop_atTop (R := ℝ))
      have hscaled :
          Tendsto (fun k : ℕ => Real.rpow (k : ℝ) α * M) atTop (𝓝 0) := by
        simpa using hkpow.mul_const M
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have heps : ∀ᶠ k : ℕ in atTop, Real.rpow (k : ℝ) α * M < ε :=
        (tendsto_order.1 hscaled).2 ε hε
      filter_upwards [heps] with k hk
      intro x
      have harg : 0 ≤ (k : ℝ) * ‖x‖ :=
        mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      have hf0 : 0 ≤ f ((k : ℝ) * ‖x‖) := hf_nonneg _ harg
      have hrpow0 : 0 ≤ Real.rpow (k : ℝ) α :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      rw [apm_a98a01_dilation, dist_zero_left, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hrpow0, abs_of_nonneg hf0]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left
          (by simpa [abs_of_nonneg hf0] using hbound _ harg)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hk
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hae_ne : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ≠ 0 := by
      have hs : (volume : Measure (EuclideanSpace ℝ (Fin n))) ({0} : Set _) = 0 := by
        have hmp := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
          (measurableSet_singleton (0 : WithLp 2 (Fin n → ℝ))).nullMeasurableSet
        simpa using hmp
      simpa only [ae_iff, compl_setOf, not_ne_iff] using hs
    constructor
    · intro hae
      obtain ⟨x, hxlim, hxne⟩ := (hae.and hae_ne).exists
      have hr : 0 < ‖x‖ := norm_pos_iff.mpr hxne
      have harg : Tendsto (fun k : ℕ => (k : ℝ) * ‖x‖) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const hr
      have hG : Tendsto
          (fun k : ℕ => (((k : ℝ) * ‖x‖) ^ 4) * f ((k : ℝ) * ‖x‖))
          atTop (𝓝 1) := hf_infty.comp harg
      have hGne : ∀ᶠ k : ℕ in atTop,
          (((k : ℝ) * ‖x‖) ^ 4) * f ((k : ℝ) * ‖x‖) ≠ 0 :=
        hG.eventually_ne one_ne_zero
      have hquot : Tendsto
          (fun k : ℕ =>
            (‖x‖ ^ 4 * apm_a98a01_dilation f α k x) /
              ((((k : ℝ) * ‖x‖) ^ 4) * f ((k : ℝ) * ‖x‖)))
          atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hxlim).div hG (by norm_num)
      have hpow : Tendsto (fun k : ℕ => Real.rpow (k : ℝ) (α - 4))
          atTop (𝓝 0) := by
        apply hquot.congr'
        filter_upwards [Nat.eventually_pos, hGne] with k hk hkG
        simpa [apm_a98a01_dilation] using
          (apm_a98a01_recover_identity f α ‖x‖ k hk hr hkG).symm
      by_contra hnot
      have hexp : 0 ≤ α - 4 := by linarith
      have hone : (1 : ℝ) ≤ 0 := ge_of_tendsto hpow (by
        filter_upwards [eventually_ge_atTop 1] with k hk
        exact Real.one_le_rpow (by exact_mod_cast hk) hexp)
      norm_num at hone
    · intro ha
      filter_upwards [hae_ne] with x hxne
      have hr : 0 < ‖x‖ := norm_pos_iff.mpr hxne
      have harg : Tendsto (fun k : ℕ => (k : ℝ) * ‖x‖) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const hr
      have hG : Tendsto
          (fun k : ℕ => (((k : ℝ) * ‖x‖) ^ 4) * f ((k : ℝ) * ‖x‖))
          atTop (𝓝 1) := hf_infty.comp harg
      have hpow : Tendsto (fun k : ℕ => Real.rpow (k : ℝ) (α - 4))
          atTop (𝓝 0) := by
        have hp := (tendsto_rpow_neg_atTop (y := 4 - α) (sub_pos.mpr ha)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
        simpa only [neg_sub] using hp
      have hprod := (hpow.div_const (‖x‖ ^ 4)).mul hG
      simp only [zero_div, zero_mul] at hprod
      apply hprod.congr'
      filter_upwards [Nat.eventually_pos] with k hk
      simpa [apm_a98a01_dilation] using
        (apm_a98a01_factor_identity f α ‖x‖ k hk hr).symm
  · let C : ℝ≥0∞ :=
      eLpNorm (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖) 1 volume
    have hCpos : 0 < C := pos_iff_ne_zero.mpr
      (apm_a98a01_radial_eLpNorm_ne_zero n hn f hf_cont hf_infty)
    constructor
    · intro hlim
      have hn3 : n ≤ 3 := by
        by_contra hn3
        have hCtop : C = ∞ := by
          have hnotlt : ¬ C < ∞ := by
            intro hlt
            exact hn3
              ((apm_a98a01_radial_eLpNorm_lt_top_iff n hn f hf_cont hf_infty).1 hlt)
          simpa only [lt_top_iff_ne_top, not_not] using hnotlt
        have hsmall : ∀ᶠ k : ℕ in atTop,
            eLpNorm (apm_a98a01_dilation (n := n) f α k) 1 volume < C :=
          hlim.eventually (Iio_mem_nhds hCpos)
        obtain ⟨k, hk, hkpos⟩ :=
          (hsmall.and (eventually_gt_atTop 0)).exists
        rw [apm_a98a01_dilation_eLpNorm_eq n hn f α k hkpos,
          show eLpNorm (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖) 1 volume = C
            from rfl,
          hCtop] at hk
        have hcoeff : 0 < ENNReal.ofReal (Real.rpow (k : ℝ) (α - n)) :=
          ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos (by exact_mod_cast hkpos) _)
        rw [ENNReal.mul_top hcoeff.ne'] at hk
        exact (lt_irrefl ∞) hk
      refine ⟨hn3, ?_⟩
      by_contra hα
      have hexp : 0 ≤ α - (n : ℝ) :=
        sub_nonneg.mpr (le_of_not_gt hα)
      have hsmall : ∀ᶠ k : ℕ in atTop,
          eLpNorm (apm_a98a01_dilation (n := n) f α k) 1 volume < C :=
        hlim.eventually (Iio_mem_nhds hCpos)
      obtain ⟨k, hk, hk1⟩ :=
        (hsmall.and (eventually_ge_atTop 1)).exists
      have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
      rw [apm_a98a01_dilation_eLpNorm_eq n hn f α k hkpos,
        show eLpNorm (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖) 1 volume = C
          from rfl] at hk
      have hrpow : 1 ≤ Real.rpow (k : ℝ) (α - n) :=
        Real.one_le_rpow (by exact_mod_cast hk1) hexp
      have hcoeff :
          (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.rpow (k : ℝ) (α - n)) :=
        ENNReal.one_le_ofReal.mpr hrpow
      have hge : C ≤ ENNReal.ofReal (Real.rpow (k : ℝ) (α - n)) * C := by
        simpa using mul_le_mul_right' hcoeff C
      exact (not_lt_of_ge hge) hk
    · rintro ⟨hn3, hα⟩
      have hCtop : C ≠ ∞ :=
        (apm_a98a01_radial_eLpNorm_lt_top_iff n hn f hf_cont hf_infty).2 hn3 |>.ne
      have hreal : Tendsto
          (fun k : ℕ => Real.rpow (k : ℝ) (α - n)) atTop (𝓝 0) := by
        have hexp : 0 < (n : ℝ) - α := sub_pos.mpr hα
        simpa only [Function.comp_apply, neg_sub] using
          (tendsto_rpow_neg_atTop hexp).comp
            (tendsto_natCast_atTop_atTop (R := ℝ))
      have hcoeff : Tendsto
          (fun k : ℕ => ENNReal.ofReal (Real.rpow (k : ℝ) (α - n)))
          atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hreal
      have hprod : Tendsto
          (fun k : ℕ => ENNReal.ofReal (Real.rpow (k : ℝ) (α - n)) * C)
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.mul_const hcoeff (Or.inr hCtop)
      apply hprod.congr'
      filter_upwards [eventually_gt_atTop 0] with k hk
      exact (apm_a98a01_dilation_eLpNorm_eq n hn f α k hk).symm
