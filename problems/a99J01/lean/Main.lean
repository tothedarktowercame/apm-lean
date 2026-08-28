import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a99J01

## Statement repairs

None.

## Encoding notes

The integral of `log |f|` may equal `-∞` when `f` vanishes. Consequently it is
encoded as an `EReal` extended integral: the difference of the lintegrals of its
positive and negative parts. At a zero of `f`, the negative part is `⊤`, correctly
representing `log 0 = -∞`; using Lean's real-valued `Real.log 0 = 0` directly would
misstate the problem.
-/

def apmLogAbsPositive {X : Type*} (f : X → ℝ) (x : X) : ENNReal :=
  ENNReal.ofReal (Real.log |f x|)

def apmLogAbsNegative {X : Type*} (f : X → ℝ) (x : X) : ENNReal :=
  if f x = 0 then ⊤ else ENNReal.ofReal (-Real.log |f x|)

noncomputable def apmLogIntegralOn {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (E : Set X) (mu : Measure X) : EReal :=
  ((∫⁻ x in E, apmLogAbsPositive f x ∂mu : ENNReal) : EReal) -
    ((∫⁻ x in E, apmLogAbsNegative f x ∂mu : ENNReal) : EReal)

/-- The positive part of the logarithm is pointwise dominated by `|f|`. -/
lemma apmLogAbsPositive_le_abs {X : Type*} (f : X → ℝ) (x : X) :
    apmLogAbsPositive f x ≤ ENNReal.ofReal |f x| := by
  exact ENNReal.ofReal_le_ofReal (Real.log_le_self (abs_nonneg (f x)))

/-- For an integrable function, the positive part of its logarithm has finite
extended integral on every measurable or nonmeasurable subset. -/
lemma apmLogAbsPositive_setLIntegral_ne_top
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ}
    (hf : Integrable f mu) (E : Set X) :
    ∫⁻ x in E, apmLogAbsPositive f x ∂mu ≠ ⊤ := by
  apply ne_top_of_le_ne_top (ne_top_of_lt hf.norm.lintegral_lt_top)
  calc
    ∫⁻ x in E, apmLogAbsPositive f x ∂mu
        ≤ ∫⁻ x in E, ENNReal.ofReal |f x| ∂mu :=
      lintegral_mono (fun x ↦ apmLogAbsPositive_le_abs f x)
    _ ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂mu := setLIntegral_le_lintegral _ _

/-- If the negative logarithmic part has infinite mass while the positive part
is finite, the custom extended integral is exactly `-∞`. -/
lemma apmLogIntegralOn_eq_bot_of_negative_eq_top
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ} {E : Set X}
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu = ⊤) :
    apmLogIntegralOn f E mu = ⊥ := by
  unfold apmLogIntegralOn
  rw [hneg]
  simp

lemma apmLogIntegralOn_le_of_negative_eq_top
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ} {E : Set X}
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu = ⊤) (r : EReal) :
    apmLogIntegralOn f E mu ≤ r := by
  rw [apmLogIntegralOn_eq_bot_of_negative_eq_top hneg]
  exact bot_le

/-- The tangent-line bound needed in the finite-negative-part branch.  This
avoids measure normalization and Jensen bookkeeping: after integration with
`m = (mu E).toReal`, the `m * |f|` term is controlled directly by `hf_norm`.
The nonzero hypothesis is available almost everywhere whenever the custom
negative logarithmic part has finite lintegral. -/
lemma apm_log_abs_le_tangent {m x : ℝ} (hm : 0 < m) (hx : x ≠ 0) :
    Real.log |x| ≤ m * |x| - Real.log m - 1 := by
  have hax : 0 < |x| := abs_pos.mpr hx
  have hmx : 0 < m * |x| := mul_pos hm hax
  have h := Real.log_le_sub_one_of_pos hmx
  rw [Real.log_mul hm.ne' hax.ne'] at h
  linarith

/-- Why this unblocks `apm_a99j01`: finiteness of the custom negative
logarithmic part rules out zeros almost everywhere on the restricted set,
which is the missing hypothesis for applying the real logarithm estimates. -/
theorem apm_a99J01_bridge_1
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ}
    (hf : Integrable f mu) {E : Set X} (hE : MeasurableSet E)
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu ≠ ⊤) :
    ∀ᵐ x ∂mu.restrict E, f x ≠ 0 := by
  have hfmeas : AEMeasurable f (mu.restrict E) :=
    hf.aestronglyMeasurable.aemeasurable.restrict
  have hnmeas : AEMeasurable (apmLogAbsNegative f) (mu.restrict E) := by
    let g := hfmeas.mk f
    have hg : Measurable g := hfmeas.measurable_mk
    have hgneg : Measurable (apmLogAbsNegative g) := by
      unfold apmLogAbsNegative
      apply Measurable.ite
      · change MeasurableSet (g ⁻¹' ({0} : Set ℝ))
        exact (measurableSet_singleton (0 : ℝ)).preimage hg
      · fun_prop
      · fun_prop
    apply hgneg.aemeasurable.congr
    filter_upwards [hfmeas.ae_eq_mk] with x hx
    simp [apmLogAbsNegative, g, hx]
  have hfinite : ∀ᵐ x ∂mu.restrict E, apmLogAbsNegative f x < ⊤ :=
    ae_lt_top' hnmeas hneg
  filter_upwards [hfinite] with x hx
  intro hzero
  simp [apmLogAbsNegative, hzero] at hx

/-- Why this unblocks `apm_a99j01`: when both logarithmic parts are finite,
the custom `EReal` subtraction is exactly the coercion of the ordinary
set integral of `log |f|`; the tangent inequality can then be integrated with
`setIntegral_mono_ae`. -/
theorem apm_a99J01_bridge_2
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ}
    (hf : Integrable f mu) {E : Set X} (hE : MeasurableSet E)
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu ≠ ⊤) :
    apmLogIntegralOn f E mu =
      ((∫ x in E, Real.log |f x| ∂mu : ℝ) : EReal) := by
  let l : X → ℝ := fun x ↦ Real.log |f x|
  let nu := mu.restrict E
  have hlmeas : AEMeasurable l nu := by
    simpa [l, nu, Real.norm_eq_abs] using
      hf.aestronglyMeasurable.aemeasurable.restrict.norm.log
  have hpos : (∫⁻ x, ENNReal.ofReal (l x) ∂nu) ≠ ⊤ := by
    simpa [l, nu, apmLogAbsPositive] using
      apmLogAbsPositive_setLIntegral_ne_top hf E
  have hnonzero : ∀ᵐ x ∂nu, f x ≠ 0 :=
    apm_a99J01_bridge_1 hf hE hneg
  have hneg_eq :
      (∫⁻ x, ENNReal.ofReal (-l x) ∂nu) =
        ∫⁻ x in E, apmLogAbsNegative f x ∂mu := by
    apply lintegral_congr_ae
    filter_upwards [hnonzero] with x hx
    simp [l, apmLogAbsNegative, hx]
  have hneg' : (∫⁻ x, ENNReal.ofReal (-l x) ∂nu) ≠ ⊤ := by
    rw [hneg_eq]
    exact hneg
  have hfinite : HasFiniteIntegral l nu := by
    rw [hasFiniteIntegral_iff_norm]
    calc
      (∫⁻ x, ENNReal.ofReal ‖l x‖ ∂nu) ≤
          ∫⁻ x, ENNReal.ofReal (l x) + ENNReal.ofReal (-l x) ∂nu := by
        apply lintegral_mono
        intro x
        rcases le_total 0 (l x) with hx | hx
        · simp [Real.norm_eq_abs, abs_of_nonneg hx, hx]
        · simp [Real.norm_eq_abs, abs_of_nonpos hx, hx]
      _ = (∫⁻ x, ENNReal.ofReal (l x) ∂nu) +
          ∫⁻ x, ENNReal.ofReal (-l x) ∂nu :=
        lintegral_add_left' hlmeas.ennreal_ofReal _
      _ < ⊤ := ENNReal.add_lt_top.mpr
        ⟨lt_top_iff_ne_top.mpr hpos, lt_top_iff_ne_top.mpr hneg'⟩
  have hl : Integrable l nu := ⟨hlmeas.aestronglyMeasurable, hfinite⟩
  unfold apmLogIntegralOn
  change ((∫⁻ x, ENNReal.ofReal (l x) ∂nu : ENNReal) : EReal) -
      ((∫⁻ x in E, apmLogAbsNegative f x ∂mu : ENNReal) : EReal) = _
  rw [← hneg_eq, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hl,
    EReal.coe_sub, EReal.coe_ennreal_toReal hpos,
    EReal.coe_ennreal_toReal hneg']

lemma apm_log_abs_integrableOn
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ}
    (hf : Integrable f mu) {E : Set X} (hE : MeasurableSet E)
    (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu ≠ ⊤) :
    IntegrableOn (fun x ↦ Real.log |f x|) E mu := by
  let l : X → ℝ := fun x ↦ Real.log |f x|
  let nu := mu.restrict E
  have hlmeas : AEMeasurable l nu := by
    simpa [l, nu, Real.norm_eq_abs] using
      hf.aestronglyMeasurable.aemeasurable.restrict.norm.log
  have hpos : (∫⁻ x, ENNReal.ofReal (l x) ∂nu) ≠ ⊤ := by
    simpa [l, nu, apmLogAbsPositive] using
      apmLogAbsPositive_setLIntegral_ne_top hf E
  have hnonzero : ∀ᵐ x ∂nu, f x ≠ 0 :=
    apm_a99J01_bridge_1 hf hE hneg
  have hneg_eq : (∫⁻ x, ENNReal.ofReal (-l x) ∂nu) =
      ∫⁻ x in E, apmLogAbsNegative f x ∂mu := by
    apply lintegral_congr_ae
    filter_upwards [hnonzero] with x hx
    simp [l, apmLogAbsNegative, hx]
  have hneg' : (∫⁻ x, ENNReal.ofReal (-l x) ∂nu) ≠ ⊤ := by
    rw [hneg_eq]
    exact hneg
  change Integrable l nu
  refine ⟨hlmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ x, ENNReal.ofReal ‖l x‖ ∂nu) ≤
        ∫⁻ x, ENNReal.ofReal (l x) + ENNReal.ofReal (-l x) ∂nu := by
      apply lintegral_mono
      intro x
      rcases le_total 0 (l x) with hx | hx
      · simp [Real.norm_eq_abs, abs_of_nonneg hx]
      · simp [Real.norm_eq_abs, abs_of_nonpos hx]
    _ = (∫⁻ x, ENNReal.ofReal (l x) ∂nu) +
        ∫⁻ x, ENNReal.ofReal (-l x) ∂nu :=
      lintegral_add_left' hlmeas.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.mpr
      ⟨lt_top_iff_ne_top.mpr hpos, lt_top_iff_ne_top.mpr hneg'⟩

theorem apm_a99j01
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : X → ℝ)
    (hf : Integrable f mu)
    (hf_norm : ∫ x, |f x| ∂mu = 1) :
    ∀ E : Set X, MeasurableSet E → 0 < mu E → mu E < ⊤ →
      apmLogIntegralOn f E mu ≤
        ((-((mu E).toReal) * Real.log (mu E).toReal : ℝ) : EReal) := by
  intro E hE hmu0 hmutop
  by_cases hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu = ⊤
  · exact apmLogIntegralOn_le_of_negative_eq_top hneg _
  · rw [apm_a99J01_bridge_2 hf hE hneg]
    apply EReal.coe_le_coe_iff.mpr
    let m := (mu E).toReal
    let nu := mu.restrict E
    have hm : 0 < m := ENNReal.toReal_pos hmu0.ne' hmutop.ne
    have hlog : Integrable (fun x ↦ Real.log |f x|) nu :=
      (apm_log_abs_integrableOn hf hE hneg).integrable
    have habs : Integrable (fun x ↦ |f x|) nu := hf.abs.restrict
    have hc : Integrable (fun _ : X ↦ Real.log m) nu := by
      change IntegrableOn (fun _ : X ↦ Real.log m) E mu
      exact integrableOn_const hmutop.ne
    have hone : Integrable (fun _ : X ↦ (1 : ℝ)) nu := by
      change IntegrableOn (fun _ : X ↦ (1 : ℝ)) E mu
      exact integrableOn_const hmutop.ne
    have hg : Integrable (fun x ↦ m * |f x| - Real.log m - 1) nu :=
      ((habs.const_mul m).sub hc).sub hone
    have hpoint : ∀ᵐ x ∂nu,
        Real.log |f x| ≤ m * |f x| - Real.log m - 1 := by
      filter_upwards [apm_a99J01_bridge_1 hf hE hneg] with x hx
      exact apm_log_abs_le_tangent hm hx
    have hmono := integral_mono_ae hlog hg hpoint
    have hEabs : ∫ x in E, |f x| ∂mu ≤ 1 := by
      rw [← hf_norm]
      exact setIntegral_le_integral hf.abs (ae_of_all _ fun x ↦ abs_nonneg (f x))
    change (∫ x, Real.log |f x| ∂nu) ≤ -m * Real.log m
    calc
      (∫ x, Real.log |f x| ∂nu) ≤
          ∫ x, (m * |f x| - Real.log m - 1) ∂nu := hmono
      _ = m * (∫ x in E, |f x| ∂mu) - m * Real.log m - m := by
        have hs1 : (∫ x, m * |f x| - Real.log m - 1 ∂nu) =
            (∫ x, m * |f x| - Real.log m ∂nu) - ∫ _ : X, 1 ∂nu :=
          integral_sub ((habs.const_mul m).sub hc) hone
        have hs2 : (∫ x, m * |f x| - Real.log m ∂nu) =
            (∫ x, m * |f x| ∂nu) - ∫ _ : X, Real.log m ∂nu :=
          integral_sub (habs.const_mul m) hc
        rw [hs1, hs2, integral_const_mul]
        simp [nu, Measure.restrict_apply_univ, m, Measure.real_def]
      _ ≤ -m * Real.log m := by nlinarith [mul_le_mul_of_nonneg_left hEabs hm.le]
