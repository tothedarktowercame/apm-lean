import Mathlib

/-!
# APM a98A04

## Statement repairs

None.  The source's informal equation `sup = ∞` is represented by its
well-typed real-valued meaning: every real height is exceeded.

## Encoding questions

None.
-/

open MeasureTheory Set

/-- The singular spike `f_{a,b}` defined in the problem. -/
noncomputable def apm_a98a04_spike (a b x : ℝ) : ℝ :=
  if a < x ∧ x < b then 1 / Real.sqrt ((b - a) * (x - a)) else 0

lemma apm_a98a04_spike_nonneg (a b x : ℝ) :
    0 ≤ apm_a98a04_spike a b x := by
  unfold apm_a98a04_spike
  split_ifs
  · positivity
  · exact le_rfl

lemma apm_a98a04_spike_eq_zero_of_not_mem
    {a b x : ℝ} (hx : x ∉ Ioo a b) :
    apm_a98a04_spike a b x = 0 := by
  rw [apm_a98a04_spike, if_neg]
  exact fun h => hx h

/-- The singular spike is measurable as a piecewise combination of elementary
measurable functions. -/
lemma apm_a98a04_spike_measurable (a b : ℝ) :
    Measurable (apm_a98a04_spike a b) := by
  change Measurable (fun x =>
    if x ∈ Ioo a b then 1 / Real.sqrt ((b - a) * (x - a)) else 0)
  apply Measurable.ite measurableSet_Ioo
  · exact measurable_const.div
      (Real.continuous_sqrt.measurable.comp
        (measurable_const.sub measurable_const |>.mul
          (measurable_id.sub measurable_const)))
  · exact measurable_const

/-- For a nondegenerate interval, the spike is strictly positive exactly on
its defining open interval. -/
lemma apm_a98a04_spike_pos_iff {a b x : ℝ} (hab : a < b) :
    0 < apm_a98a04_spike a b x ↔ x ∈ Ioo a b := by
  constructor
  · intro hpos
    by_contra hx
    rw [apm_a98a04_spike_eq_zero_of_not_mem hx] at hpos
    exact (lt_irrefl 0 hpos)
  · intro hx
    unfold apm_a98a04_spike
    rw [if_pos ⟨hx.1, hx.2⟩]
    exact one_div_pos.mpr (Real.sqrt_pos.2
      (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hx.1)))

/-- The strict positivity set of a nondegenerate spike is literally its open
support interval. -/
lemma apm_a98a04_spike_pos_set {a b : ℝ} (hab : a < b) :
    {x : ℝ | 0 < apm_a98a04_spike a b x} = Ioo a b := by
  ext x
  exact apm_a98a04_spike_pos_iff hab

/-- In particular, the positivity set has strictly positive Lebesgue measure.
This is the measure-theoretic input needed to make later height assertions
survive replacement by an almost-everywhere equal representative. -/
lemma apm_a98a04_spike_pos_set_measure_pos {a b : ℝ} (hab : a < b) :
    0 < volume {x : ℝ | 0 < apm_a98a04_spike a b x} := by
  rw [apm_a98a04_spike_pos_set hab, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

/-- Why this unblocks the first conjunct of `apm_a98a04`: this is the
translated inverse-square-root integral, including both integrability and the
exact normalization independent of the interval endpoints. -/
theorem apm_a98A04_bridge_1
    (a b : ℝ) (hab : a < b) :
    Integrable (apm_a98a04_spike a b) volume ∧
      ∫ x : ℝ, apm_a98a04_spike a b x ∂volume = 2 := by
  let r : ℝ := -(1 / 2 : ℝ)
  let q : ℝ → ℝ := fun x => x ^ r
  let C : ℝ := 1 / Real.sqrt (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  have hqOn : IntegrableOn q (Ioo 0 (b - a)) volume := by
    apply (intervalIntegral.integrableOn_Ioo_rpow_iff hba).2
    dsimp [r]
    norm_num
  have hqII : IntervalIntegrable q volume 0 (b - a) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hba.le).2 hqOn
  have htransII : IntervalIntegrable (fun x => q (x - a)) volume a b := by
    convert hqII.comp_sub_right a using 1 <;> ring
  have htransOn :
      IntegrableOn (fun x => C * q (x - a)) (Ioo a b) volume := by
    have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 htransII
    exact h.const_mul C
  have hfun : apm_a98a04_spike a b =
      (Ioo a b).indicator (fun x => C * q (x - a)) := by
    funext x
    by_cases hx : x ∈ Ioo a b
    · rw [indicator_of_mem hx]
      simp only [apm_a98a04_spike, hx.1, hx.2, and_self, ↓reduceIte]
      dsimp [C, q, r]
      rw [Real.sqrt_mul hba.le, div_eq_mul_inv, one_mul, mul_inv,
        Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_neg (sub_pos.mpr hx.1).le]
      norm_num
    · have hz : apm_a98a04_spike a b x = 0 := by
        unfold apm_a98a04_spike
        have hn : ¬(a < x ∧ x < b) := fun h => hx h
        rw [if_neg hn]
      rw [hz]
      simp [hx]
  constructor
  · rw [hfun, integrable_indicator_iff measurableSet_Ioo]
    exact htransOn
  · rw [hfun, integral_indicator measurableSet_Ioo,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab.le]
    dsimp [q, C]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_sub_right (fun y : ℝ => y ^ r) a]
    simp only [sub_self]
    rw [integral_rpow (by left; dsimp [r]; norm_num)]
    dsimp [r]
    rw [Real.zero_rpow (by norm_num)]
    rw [Real.sqrt_eq_rpow]
    field_simp
    norm_num

/-- Why this unblocks the a.e.-robust height argument in `apm_a98a04`:
every finite-height superlevel of a spike contains a genuine open subinterval,
and hence has positive measure rather than merely containing isolated points. -/
theorem apm_a98A04_bridge_2
    (a b M : ℝ) (hab : a < b) :
    ∃ c d : ℝ, a < c ∧ c < d ∧ d < b ∧
      Ioo c d ⊆ {x : ℝ | M < apm_a98a04_spike a b x} := by
  let K : ℝ := |M| + 1
  let δ : ℝ := min ((b - a) / 4) (1 / (4 * (b - a) * K ^ 2))
  have hba : 0 < b - a := sub_pos.mpr hab
  have hK : 0 < K := by dsimp [K]; positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · positivity
    · positivity
  have hδba : 2 * δ < b - a := by
    have hle : δ ≤ (b - a) / 4 := min_le_left _ _
    linarith
  refine ⟨a + δ, a + 2 * δ, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · intro x hx
    change M < apm_a98a04_spike a b x
    have hax : a < x := by linarith [hx.1]
    have hxb : x < b := by linarith [hx.2, hδba]
    rw [apm_a98a04_spike, if_pos ⟨hax, hxb⟩]
    have hxδ : x - a < 2 * δ := by linarith [hx.2]
    have hδle : δ ≤ 1 / (4 * (b - a) * K ^ 2) := min_le_right _ _
    have hprodpos : 0 < (b - a) * (x - a) := mul_pos hba (sub_pos.mpr hax)
    have hbound : (b - a) * (x - a) < 1 / K ^ 2 := by
      calc
        (b - a) * (x - a) < (b - a) * (2 * δ) :=
          mul_lt_mul_of_pos_left hxδ hba
        _ ≤ (b - a) * (2 * (1 / (4 * (b - a) * K ^ 2))) := by
          gcongr
        _ < 1 / K ^ 2 := by
          field_simp
          nlinarith [sq_pos_of_pos hK, hba]
    have hsqrt : Real.sqrt ((b - a) * (x - a)) < 1 / K := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / K),
        Real.sqrt_lt_sqrt_iff hprodpos.le]
      simpa [div_pow] using hbound
    have hrecip : K < 1 / Real.sqrt ((b - a) * (x - a)) := by
      rw [lt_div_iff₀ (Real.sqrt_pos.2 hprodpos)]
      have := mul_lt_mul_of_pos_left hsqrt hK
      field_simp at this
      exact this
    have hMK : M < K := by dsimp [K]; linarith [le_abs_self M]
    exact hMK.trans hrecip

/-- Rational endpoint pairs index the countable family of local spikes. -/
abbrev apm_a98a04_index := ℚ × ℚ

/-- A positive summable weight assigned injectively to every rational pair. -/
noncomputable def apm_a98a04_weight (i : apm_a98a04_index) : ℝ :=
  (1 / 2 : ℝ) ^ Encodable.encode i

/-- The weighted spike associated to a rational pair, with degenerate pairs
discarded. -/
noncomputable def apm_a98a04_term (i : apm_a98a04_index) (x : ℝ) : ℝ :=
  if (i.1 : ℝ) < i.2 then
    apm_a98a04_weight i * apm_a98a04_spike i.1 i.2 x
  else 0

lemma apm_a98a04_weight_pos (i : apm_a98a04_index) :
    0 < apm_a98a04_weight i := by
  unfold apm_a98a04_weight
  positivity

lemma apm_a98a04_weight_summable : Summable apm_a98a04_weight := by
  exact summable_geometric_two_encode

lemma apm_a98a04_term_nonneg (i : apm_a98a04_index) (x : ℝ) :
    0 ≤ apm_a98a04_term i x := by
  unfold apm_a98a04_term
  split_ifs
  · exact mul_nonneg (apm_a98a04_weight_pos i).le
      (apm_a98a04_spike_nonneg _ _ _)
  · exact le_rfl

lemma apm_a98a04_term_integrable (i : apm_a98a04_index) :
    Integrable (apm_a98a04_term i) volume := by
  unfold apm_a98a04_term
  split_ifs with h
  · exact (apm_a98A04_bridge_1 (i.1 : ℝ) (i.2 : ℝ) h).1.const_mul _
  · exact integrable_zero _ _ _

lemma apm_a98a04_term_integral_norm (i : apm_a98a04_index) :
    (∫ x, ‖apm_a98a04_term i x‖ ∂volume) =
      if (i.1 : ℝ) < i.2 then 2 * apm_a98a04_weight i else 0 := by
  unfold apm_a98a04_term
  split_ifs with h
  · have hw := (apm_a98a04_weight_pos i).le
    simp_rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hw (apm_a98a04_spike_nonneg _ _ _))]
    rw [integral_const_mul,
      (apm_a98A04_bridge_1 (i.1 : ℝ) (i.2 : ℝ) h).2]
    ring
  · simp

lemma apm_a98a04_term_integral_norm_summable :
    Summable (fun i : apm_a98a04_index =>
      ∫ x, ‖apm_a98a04_term i x‖ ∂volume) := by
  apply Summable.of_nonneg_of_le
    (f := fun i => 2 * apm_a98a04_weight i)
  · intro i
    exact integral_nonneg fun x => norm_nonneg _
  · intro i
    rw [apm_a98a04_term_integral_norm]
    by_cases h : (i.1 : ℝ) < i.2
    · simp [h]
    · simp [h, (apm_a98a04_weight_pos i).le]
  · exact apm_a98a04_weight_summable.mul_left 2

/-- Every real open interval contains one of the indexed nondegenerate
rational intervals. -/
lemma apm_a98a04_exists_index_inside {α β : ℝ} (h : α < β) :
    ∃ i : apm_a98a04_index,
      α < (i.1 : ℝ) ∧ (i.1 : ℝ) < i.2 ∧ (i.2 : ℝ) < β := by
  obtain ⟨q, hαq, hqβ⟩ := exists_rat_btwn h
  obtain ⟨r, hqr, hrβ⟩ := exists_rat_btwn hqβ
  exact ⟨(q, r), hαq, hqr, hrβ⟩

/-- A duplicate-free natural-number enumeration of the rational-pair terms.
Numbers outside the range of `Encodable.encode` contribute zero. -/
noncomputable def apm_a98a04_seq (n : ℕ) (x : ℝ) : ℝ :=
  match Encodable.decode (α := apm_a98a04_index) n with
  | some i => if Encodable.encode i = n then apm_a98a04_term i x else 0
  | none => 0

lemma apm_a98a04_seq_encode (i : apm_a98a04_index) :
    apm_a98a04_seq (Encodable.encode i) = apm_a98a04_term i := by
  funext x
  simp [apm_a98a04_seq]

lemma apm_a98a04_seq_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ apm_a98a04_seq n x := by
  cases hdec : Encodable.decode (α := apm_a98a04_index) n with
  | none =>
      unfold apm_a98a04_seq
      rw [hdec]
  | some i =>
      unfold apm_a98a04_seq
      rw [hdec]
      dsimp only
      split_ifs
      · exact apm_a98a04_term_nonneg _ _
      · exact le_rfl

lemma apm_a98a04_seq_integrable (n : ℕ) :
    Integrable (apm_a98a04_seq n) volume := by
  cases hdec : Encodable.decode (α := apm_a98a04_index) n with
  | none =>
      unfold apm_a98a04_seq
      rw [hdec]
      dsimp only
      exact integrable_zero _ _ _
  | some i =>
      unfold apm_a98a04_seq
      rw [hdec]
      dsimp only
      split_ifs
      · exact apm_a98a04_term_integrable _
      · exact integrable_zero _ _ _

lemma apm_a98a04_seq_integral_norm_le (n : ℕ) :
    (∫ x, ‖apm_a98a04_seq n x‖ ∂volume) ≤ 2 * (1 / 2 : ℝ) ^ n := by
  cases hdec : Encodable.decode (α := apm_a98a04_index) n with
  | none =>
      simp [apm_a98a04_seq, hdec]
  | some i =>
      simp only [apm_a98a04_seq, hdec]
      split_ifs with henc
      · rw [apm_a98a04_term_integral_norm]
        by_cases hv : (i.1 : ℝ) < i.2
        · simp only [if_pos hv, apm_a98a04_weight]
          rw [henc]
        · simp [hv]
      · simp

lemma apm_a98a04_seq_integral_norm_summable :
    Summable (fun n : ℕ => ∫ x, ‖apm_a98a04_seq n x‖ ∂volume) := by
  apply Summable.of_nonneg_of_le
    (f := fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n)
  · intro n
    exact integral_nonneg fun x => norm_nonneg _
  · exact apm_a98a04_seq_integral_norm_le
  · exact summable_geometric_two.mul_left 2

/-- The weighted spike series is absolutely summable at almost every point. -/
lemma apm_a98a04_seq_summable_ae :
    ∀ᵐ x ∂volume, Summable (fun n => apm_a98a04_seq n x) := by
  have hmeas (n : ℕ) : AEMeasurable (fun x => ‖apm_a98a04_seq n x‖ₑ) volume :=
    (apm_a98a04_seq_integrable n).aestronglyMeasurable.enorm
  have hlin (n : ℕ) :
      ∫⁻ x, ‖apm_a98a04_seq n x‖ₑ ∂volume =
        ‖∫ x, ‖apm_a98a04_seq n x‖ ∂volume‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (apm_a98a04_seq_integrable n).norm]
    simp only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)]
  have htop :
      (∑' n, (∫⁻ x, ‖apm_a98a04_seq n x‖ₑ ∂volume)) ≠
        (⊤ : ENNReal) := by
    rw [funext hlin]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 apm_a98a04_seq_integral_norm_summable.abs
  rw [← lintegral_tsum hmeas] at htop
  have hsummable_norm :
      ∀ᵐ x ∂volume, Summable (fun n => (‖apm_a98a04_seq n x‖₊ : ℝ)) := by
    refine (ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) htop).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  exact hsummable_norm.mono fun x hx => hx.of_norm

/-- The pointwise sum of term norms is an integrable real-valued dominator. -/
lemma apm_a98a04_seq_norm_tsum_integrable :
    Integrable (fun x : ℝ => (↑(∑' n, ‖apm_a98a04_seq n x‖₊) : ℝ)) volume := by
  let B : ℝ → ℝ := fun x => (↑(∑' n, ‖apm_a98a04_seq n x‖₊) : ℝ)
  have hBmeas : AEStronglyMeasurable B volume := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.coe_nnreal_real
    apply AEMeasurable.nnreal_tsum
    exact fun n =>
      (apm_a98a04_seq_integrable n).aestronglyMeasurable.nnnorm.aemeasurable
  have hmeas (n : ℕ) : AEMeasurable (fun x => ‖apm_a98a04_seq n x‖ₑ) volume :=
    (apm_a98a04_seq_integrable n).aestronglyMeasurable.enorm
  have hlin (n : ℕ) :
      ∫⁻ x, ‖apm_a98a04_seq n x‖ₑ ∂volume =
        ‖∫ x, ‖apm_a98a04_seq n x‖ ∂volume‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (apm_a98a04_seq_integrable n).norm]
    simp only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)]
  have htop :
      (∑' n, (∫⁻ x, ‖apm_a98a04_seq n x‖ₑ ∂volume)) ≠
        (⊤ : ENNReal) := by
    rw [funext hlin]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 apm_a98a04_seq_integral_norm_summable.abs
  refine ⟨hBmeas, ?_⟩
  have hfinite :
      ∫⁻ x, ∑' n, ‖apm_a98a04_seq n x‖ₑ ∂volume < ⊤ := by
    rw [lintegral_tsum hmeas]
    exact lt_top_iff_ne_top.2 htop
  change (∫⁻ x, ‖(↑(∑' n, ‖apm_a98a04_seq n x‖₊) : ℝ)‖ₑ ∂volume) < ⊤
  refine (lintegral_congr_ae ?_).trans_lt hfinite
  filter_upwards [apm_a98a04_seq_summable_ae] with x hx
  dsimp [enorm]
  rw [Real.nnnorm_of_nonneg (NNReal.coe_nonneg _)]
  exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx.norm)

/-- The real-valued pointwise spike series is integrable. -/
lemma apm_a98a04_tsum_integrable :
    Integrable (fun x : ℝ => ∑' n, apm_a98a04_seq n x) volume := by
  have hpartial (N : ℕ) : AEStronglyMeasurable
      (fun x : ℝ => ∑ n ∈ Finset.range N, apm_a98a04_seq n x) volume := by
    exact Finset.aestronglyMeasurable_fun_sum _ fun n _ =>
      (apm_a98a04_seq_integrable n).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ∑' n, apm_a98a04_seq n x) volume := by
    apply aestronglyMeasurable_of_tendsto_ae Filter.atTop hpartial
    filter_upwards [apm_a98a04_seq_summable_ae] with x hx
    exact hx.hasSum.tendsto_sum_nat
  apply Integrable.mono' apm_a98a04_seq_norm_tsum_integrable hmeas
  filter_upwards [apm_a98a04_seq_summable_ae] with x hx
  rw [NNReal.coe_tsum]
  exact norm_tsum_le_tsum_norm hx.norm

/-- Why this unblocks the global construction in `apm_a98a04`: this is the
summable dense enumeration of weighted spikes, with its conclusion stated in
the representative-invariant form needed by the frozen theorem. -/
theorem apm_a98A04_bridge_3 :
    ∃ f : ℝ → ℝ,
      Integrable f volume ∧
      ∀ (g : ℝ → ℝ), g =ᵐ[volume] f →
        ∀ α β : ℝ, α < β →
          ∀ M : ℝ, ∃ x ∈ Ioo α β, M < g x := by
  let f : ℝ → ℝ := fun x => ∑' n, apm_a98a04_seq n x
  refine ⟨f, apm_a98a04_tsum_integrable, ?_⟩
  intro g hgf α β hαβ M
  obtain ⟨i, hαi, hiv, hiβ⟩ := apm_a98a04_exists_index_inside hαβ
  have hwi : 0 < apm_a98a04_weight i := apm_a98a04_weight_pos i
  obtain ⟨c, d, hic, hcd, hdi, hsuper⟩ :=
    apm_a98A04_bridge_2 (i.1 : ℝ) (i.2 : ℝ)
      (M / apm_a98a04_weight i) hiv
  have hmeasure : volume (Ioo c d) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd))
  letI : (ae (volume.restrict (Ioo c d))).NeBot :=
    ae_restrict_neBot.mpr hmeasure
  have hgf' : ∀ᵐ x ∂volume.restrict (Ioo c d), g x = f x := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact hgf.mono fun x hx _ => hx
  have hsum' : ∀ᵐ x ∂volume.restrict (Ioo c d),
      Summable (fun n => apm_a98a04_seq n x) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact apm_a98a04_seq_summable_ae.mono fun x hx _ => hx
  have hevent : ∀ᵐ x ∂volume.restrict (Ioo c d),
      x ∈ Ioo c d ∧ g x = f x ∧ Summable (fun n => apm_a98a04_seq n x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hgf', hsum'] with x hx hgx hsx
    exact ⟨hx, hgx, hsx⟩
  obtain ⟨x, hxcd, hgx, hsx⟩ := hevent.exists
  refine ⟨x, ⟨hαi.trans (hic.trans hxcd.1),
    hxcd.2.trans (hdi.trans hiβ)⟩, ?_⟩
  rw [hgx]
  have hterm : M < apm_a98a04_term i x := by
    unfold apm_a98a04_term
    rw [if_pos hiv]
    have hs := hsuper hxcd
    simpa [mul_comm] using (div_lt_iff₀ hwi).mp hs
  exact hterm.trans_le <| by
    rw [← apm_a98a04_seq_encode i]
    exact hsx.le_tsum (Encodable.encode i) fun n _ =>
      apm_a98a04_seq_nonneg n x

theorem apm_a98a04 :
    (∀ a b : ℝ, a < b →
      Integrable (apm_a98a04_spike a b) volume ∧
      ∫ x : ℝ, apm_a98a04_spike a b x ∂volume = 2) ∧
    (∃ f : ℝ → ℝ,
      Integrable f volume ∧
      ∀ (g : ℝ → ℝ), g =ᵐ[volume] f →
        ∀ α β : ℝ, α < β →
          ∀ M : ℝ, ∃ x ∈ Ioo α β, M < g x) := by
  constructor
  · exact apm_a98A04_bridge_1
  · exact apm_a98A04_bridge_3
