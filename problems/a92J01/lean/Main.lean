import Mathlib

/-!
# APM a92J01 — four inclusion assertions for Lᵖ spaces

## Statement repairs

The complete four-item alist was recovered from `problems/a92J01/problem.tex`.
The rendered bundle description had incorrectly been reported as truncated.
The false assertions are stated through concrete counterexamples.

## Encoding questions

None. Function-space membership is represented by `MeasureTheory.MemLp` for
restricted Lebesgue measure, Lebesgue measure on `ℝ`, and counting measure on
`ℕ`.
-/

open MeasureTheory Set

noncomputable section

def apm_a92J01_unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

def apm_a92J01_ellCounterexample (p q : ℝ) (n : ℕ) : ℝ :=
  (n.succ : ℝ) ^ (-((1 / p + 1 / q) / 2))

def apm_a92J01_realCounterexample (p q x : ℝ) : ℝ :=
  if 1 ≤ |x| then |x| ^ (-((1 / p + 1 / q) / 2)) else 0

def apm_a92J01_discontinuousCounterexample (x : ℝ) : ℝ :=
  Set.indicator (Icc (0 : ℝ) (1 / 2)) (fun _ ↦ (1 : ℝ)) x

/-- On the finite interval, the standard monotonicity of `Lᵖ` exponents
closes the first assertion directly. -/
lemma apm_a92J01_memLp_mono_on_unitMeasure
    (p q : ℝ) (hpq : q < p) (f : ℝ → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) apm_a92J01_unitMeasure) :
    MemLp f (ENNReal.ofReal q) apm_a92J01_unitMeasure := by
  letI : IsFiniteMeasure apm_a92J01_unitMeasure := by
    unfold apm_a92J01_unitMeasure
    infer_instance
  exact hf.mono_exponent (ENNReal.ofReal_le_ofReal hpq.le)

/-- The step-function counterexample is in every finite `Lᵖ` space on the
unit interval; only its discontinuity is relevant to the final assertion. -/
lemma apm_a92J01_discontinuousCounterexample_memLp (p : ℝ) :
    MemLp apm_a92J01_discontinuousCounterexample
      (ENNReal.ofReal p) apm_a92J01_unitMeasure := by
  letI : IsFiniteMeasure apm_a92J01_unitMeasure := by
    unfold apm_a92J01_unitMeasure
    infer_instance
  unfold apm_a92J01_discontinuousCounterexample
  apply memLp_indicator_const
  · exact measurableSet_Icc
  · right
    exact measure_ne_top _ _

/-- The indicator jumps at the right endpoint of its support. -/
lemma apm_a92J01_discontinuousCounterexample_not_continuousOn :
    ¬ContinuousOn apm_a92J01_discontinuousCounterexample (Icc 0 1) := by
  intro hcont
  have hhalf := hcont (1 / 2 : ℝ) (by constructor <;> norm_num)
  rw [Metric.continuousWithinAt_iff] at hhalf
  obtain ⟨δ, hδ, hclose⟩ := hhalf (1 / 2) (by norm_num)
  let d : ℝ := min (δ / 2) (1 / 4)
  let y : ℝ := 1 / 2 + d
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (half_pos hδ) (by norm_num)
  have hdδ : d < δ := by
    dsimp [d]
    calc
      min (δ / 2) (1 / 4) ≤ δ / 2 := min_le_left _ _
      _ < δ := half_lt_self hδ
  have hy : y ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [y]
      linarith
    · dsimp [y, d]
      have := min_le_right (δ / 2) (1 / 4)
      linarith
  have hydist : dist y (1 / 2 : ℝ) < δ := by
    rw [Real.dist_eq]
    dsimp [y]
    ring_nf
    rw [abs_of_pos hd]
    exact hdδ
  have hvalue := hclose hy hydist
  have hyout : y ∉ Icc (0 : ℝ) (1 / 2) := by
    intro hy'
    dsimp [y] at hy'
    linarith [hy'.2]
  have hyout' : ¬(0 ≤ y ∧ y ≤ (1 / 2 : ℝ)) := hyout
  unfold apm_a92J01_discontinuousCounterexample at hvalue
  norm_num [Set.indicator, hyout'] at hvalue

/-- The `p`th power of either power-law counterexample has exponent below
`-1`, the convergence side of both the p-series and tail-integral tests. -/
lemma apm_a92J01_p_exponent_lt_neg_one
    {p q : ℝ} (hq : 1 ≤ q) (hpq : q < p) :
    -((1 / p + 1 / q) / 2) * p < -1 := by
  have hp : 0 < p := lt_of_lt_of_le (by linarith : 0 < q) hpq.le
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hq
  field_simp
  nlinarith

/-- The corresponding `q`th-power exponent is not below `-1`, giving the
divergence side of the same two tests. -/
lemma apm_a92J01_neg_one_le_q_exponent
    {p q : ℝ} (hq : 1 ≤ q) (hpq : q < p) :
    -1 ≤ -((1 / p + 1 / q) / 2) * q := by
  have hp : 0 < p := lt_of_lt_of_le (by linarith : 0 < q) hpq.le
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hq
  field_simp
  nlinarith

/-- Why this unblocks the sequence-space conjunct of `apm_a92j01`: it
converts `MemLp` for counting measure into the shifted p-series criterion for
the concrete sequence `(n+1)⁻ᵅ`, using the two scalar exponent bounds above. -/
theorem apm_a92J01_bridge_1
    (p q : ℝ) (hq : 1 ≤ q) (hpq : q < p) :
    MemLp (apm_a92J01_ellCounterexample p q)
        (ENNReal.ofReal p) Measure.count ∧
      ¬MemLp (apm_a92J01_ellCounterexample p q)
        (ENNReal.ofReal q) Measure.count := by
  have hp : 0 < p := lt_of_lt_of_le (by linarith : (0 : ℝ) < q) hpq.le
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hq
  have hmeas : AEStronglyMeasurable
      (apm_a92J01_ellCounterexample p q) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  have hpt : ∀ r : ℝ, 0 < r → ∀ n : ℕ,
      ‖‖apm_a92J01_ellCounterexample p q n‖ ^ (ENNReal.ofReal r).toReal‖
        = ((n.succ : ℝ) ^ (-((1 / p + 1 / q) / 2) * r)) := by
    intro r hr n
    have hpos : 0 < (n.succ : ℝ) := Nat.cast_pos.mpr n.succ_pos
    have hnn : 0 ≤ ‖apm_a92J01_ellCounterexample p q n‖ ^
        (ENNReal.ofReal r).toReal :=
      Real.rpow_nonneg (norm_nonneg _) _
    have h1 : ‖apm_a92J01_ellCounterexample p q n‖ ^
        (ENNReal.ofReal r).toReal
        = ((n.succ : ℝ) ^ (-((1 / p + 1 / q) / 2) * r)) := by
      unfold apm_a92J01_ellCounterexample
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le _),
        ENNReal.toReal_ofReal hr.le, Real.rpow_mul hpos.le]
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, h1]
  constructor
  · refine (integrable_norm_rpow_iff (p := ENNReal.ofReal p) hmeas
      (by simpa [ENNReal.ofReal_eq_zero] using hp) (by simp)).mp ?_
    rw [integrable_count_iff]
    have hsum : Summable (fun n : ℕ =>
        ((n.succ : ℝ) ^ (-((1 / p + 1 / q) / 2) * p))) := by
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff
          (f := fun n : ℕ => ((n : ℝ) ^ (-((1 / p + 1 / q) / 2) * p))) 1).mpr
          (Real.summable_nat_rpow.mpr
            (apm_a92J01_p_exponent_lt_neg_one hq hpq))
    exact hsum.congr fun n => (hpt p hp n).symm
  · intro hmem
    have hint := (integrable_norm_rpow_iff (p := ENNReal.ofReal q) hmeas
      (by simpa [ENNReal.ofReal_eq_zero] using hq0) (by simp)).mpr hmem
    rw [integrable_count_iff] at hint
    have hnosum : ¬ Summable (fun n : ℕ =>
        ((n.succ : ℝ) ^ (-((1 / p + 1 / q) / 2) * q))) := by
      intro hsum
      have hshift := (summable_nat_add_iff
        (f := fun n : ℕ => ((n : ℝ) ^ (-((1 / p + 1 / q) / 2) * q))) 1).mp
        (by simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hsum)
      have hlt := Real.summable_nat_rpow.mp hshift
      exact absurd hlt (not_lt.mpr (apm_a92J01_neg_one_le_q_exponent hq hpq))
    exact hnosum (hint.congr fun n => (hpt q hq0 n))

/-- Why this unblocks the real-line conjunct of `apm_a92j01`: it converts the
indicator-supported power tail to the improper-integral criterion on
`[1,∞)`, including measurability and the two symmetric tails. -/
theorem apm_a92J01_bridge_2
    (p q : ℝ) (hq : 1 ≤ q) (hpq : q < p) :
    MemLp (apm_a92J01_realCounterexample p q)
        (ENNReal.ofReal p) volume ∧
      ¬MemLp (apm_a92J01_realCounterexample p q)
        (ENNReal.ofReal q) volume := by
  have hp : 0 < p := lt_of_lt_of_le (by linarith : (0 : ℝ) < q) hpq.le
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hq
  have hmeas : AEStronglyMeasurable
      (apm_a92J01_realCounterexample p q) volume :=
    (Measurable.ite (measurableSet_le measurable_const measurable_abs)
      (by fun_prop) measurable_const).aestronglyMeasurable
  have hcollapse : ∀ r : ℝ, 0 < r → ∀ x : ℝ, 1 < x →
      ‖apm_a92J01_realCounterexample p q x‖ ^ (ENNReal.ofReal r).toReal
        = x ^ (-((1 / p + 1 / q) / 2) * r) := by
    intro r hr x hx
    have hxabs : |x| = x := abs_of_pos (by linarith)
    have hx0 : 0 ≤ |x| := abs_nonneg x
    rw [apm_a92J01_realCounterexample,
      if_pos (by rw [hxabs]; linarith),
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx0 _),
      ENNReal.toReal_ofReal hr.le,
      ← Real.rpow_mul hx0, hxabs]
  constructor
  · refine (integrable_norm_rpow_iff (p := ENNReal.ofReal p) hmeas
      (by simpa [ENNReal.ofReal_eq_zero] using hp) (by simp)).mp ?_
    have hOn : IntegrableOn
        (fun x : ℝ => x ^ (-((1 / p + 1 / q) / 2) * p))
        (Ioi (1 : ℝ)) volume :=
      integrableOn_Ioi_rpow_of_lt
        (apm_a92J01_p_exponent_lt_neg_one hq hpq) one_pos
    have hpos : Integrable
        ((Ioi (1 : ℝ)).indicator
          (fun x : ℝ => x ^ (-((1 / p + 1 / q) / 2) * p))) volume :=
      (integrable_indicator_iff measurableSet_Ioi).2 hOn
    have hneg : Integrable
        (fun x : ℝ => (Ioi (1 : ℝ)).indicator
          (fun x : ℝ => x ^ (-((1 / p + 1 / q) / 2) * p)) (-x)) volume :=
      hpos.comp_neg
    refine (hpos.add hneg).congr ?_
    filter_upwards [Measure.ae_ne volume 1, Measure.ae_ne volume (-1 : ℝ)] with x hne1 hneneg1
    by_cases hx1 : 1 < x
    · have hnotmemneg : -x ∉ Ioi (1 : ℝ) := by
        intro hmem
        have : (1 : ℝ) < -x := hmem
        linarith
      rw [hcollapse p hp x hx1]
      simp only [Pi.add_apply]
      rw [Set.indicator_of_mem (by simpa using hx1),
        Set.indicator_of_notMem hnotmemneg]
      ring
    · by_cases hx2 : 1 < -x
      · have hxa : |x| = -x := abs_of_neg (by linarith : x < 0)
        have hx0 : 0 ≤ |x| := abs_nonneg x
        have hnotmemx : x ∉ Ioi (1 : ℝ) := by
          intro hmem
          have : (1 : ℝ) < x := by simpa using hmem
          exact hx1 this
        simp only [Pi.add_apply]
        rw [ENNReal.toReal_ofReal hp.le,
          apm_a92J01_realCounterexample,
          if_pos (by rw [hxa]; linarith),
          Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hx0 _),
          ← Real.rpow_mul hx0, hxa,
          Set.indicator_of_notMem hnotmemx,
          Set.indicator_of_mem (by simpa using hx2)]
        ring
      · have hxabsle : |x| ≤ 1 := by
          by_contra h
          have hbig : (1 : ℝ) < |x| := by
            push_neg at h
            linarith
          rcases lt_abs.mp hbig with hx | hx
          · exact hx1 hx
          · exact hx2 hx
        have hnotbig : ¬ 1 ≤ |x| := by
          intro hbig
          have hxeq : |x| = 1 := le_antisymm hxabsle hbig
          by_cases hx0 : 0 ≤ x
          · exact hne1 (by
              have := abs_of_nonneg hx0
              linarith)
          · exact hneneg1 (by
              have := abs_of_neg (by linarith : x < 0)
              linarith)
        simp only [Pi.add_apply]
        rw [ENNReal.toReal_ofReal hp.le,
          apm_a92J01_realCounterexample,
          if_neg hnotbig,
          Real.norm_eq_abs, abs_zero,
          Real.zero_rpow hp.ne']
        rw [Set.indicator_of_notMem (by
            intro hmem
            have : (1 : ℝ) < x := hmem
            linarith),
          Set.indicator_of_notMem (by
            intro hmem
            have : (1 : ℝ) < -x := hmem
            linarith)]
        ring
  · intro hmem
    have hint := (integrable_norm_rpow_iff (p := ENNReal.ofReal q) hmeas
      (by simpa [ENNReal.ofReal_eq_zero] using hq0) (by simp)).mpr hmem
    rw [ENNReal.toReal_ofReal hq0.le] at hint
    have hOn : IntegrableOn
        (fun x : ℝ => ‖apm_a92J01_realCounterexample p q x‖ ^ q)
        (Ioi (1 : ℝ)) volume := hint.integrableOn
    have hOn' : IntegrableOn
        (fun x : ℝ => ‖apm_a92J01_realCounterexample p q x‖ ^ (ENNReal.ofReal q).toReal)
        (Ioi (1 : ℝ)) volume := by
      simpa [ENNReal.toReal_ofReal hq0.le] using hOn
    have hconv : IntegrableOn
        (fun x : ℝ => x ^ (-((1 / p + 1 / q) / 2) * q))
        (Ioi (1 : ℝ)) volume := by
      refine hOn'.congr_fun (fun x hx => ?_) measurableSet_Ioi
      simpa [ENNReal.toReal_ofReal hq0.le] using hcollapse q hq0 x hx
    have hlt := (integrableOn_Ioi_rpow_iff
      (by norm_num : (0 : ℝ) < 1)).mp hconv
    exact absurd hlt (not_lt.mpr (apm_a92J01_neg_one_le_q_exponent hq hpq))

theorem apm_a92j01 :
    (∀ (p q : ℝ), 1 ≤ q → q < p → ∀ f : ℝ → ℝ,
      MemLp f (ENNReal.ofReal p) apm_a92J01_unitMeasure →
      MemLp f (ENNReal.ofReal q) apm_a92J01_unitMeasure) ∧
    (∀ (p q : ℝ), 1 ≤ q → q < p →
      MemLp (apm_a92J01_ellCounterexample p q) (ENNReal.ofReal p) Measure.count ∧
      ¬MemLp (apm_a92J01_ellCounterexample p q) (ENNReal.ofReal q) Measure.count) ∧
    (∀ (p q : ℝ), 1 ≤ q → q < p →
      MemLp (apm_a92J01_realCounterexample p q) (ENNReal.ofReal p) volume ∧
      ¬MemLp (apm_a92J01_realCounterexample p q) (ENNReal.ofReal q) volume) ∧
    (∀ p : ℝ, 2 < p →
      MemLp apm_a92J01_discontinuousCounterexample
        (ENNReal.ofReal p) apm_a92J01_unitMeasure ∧
      ¬ContinuousOn apm_a92J01_discontinuousCounterexample (Icc 0 1)) := by
  /-
  CLOSER HOP 3: the first conjunct is closed by the compiled helper
  `apm_a92J01_memLp_mono_on_unitMeasure`, using Mathlib's
  `MemLp.mono_exponent` and the existing finite-measure instance for
  `volume.restrict (Icc 0 1)`.

  Searches of the p-series, `memLp_norm_rpow_iff`, counting-measure, and
  interval-integrability APIs found all scalar ingredients for the two
  power-law counterexamples, but no packaged equivalence reducing these exact
  real-exponent `MemLp` goals to `Real.summable_nat_rpow` and
  `integrableOn_Ici_rpow_iff`.  Those coercion and measurability conversions
  remain the main bridge.  The compiled helper
  `apm_a92J01_discontinuousCounterexample_memLp` closes the membership half
  of the last conjunct through `memLp_indicator_const`. Hop 2 additionally
  closes its one-sided discontinuity half in
  `apm_a92J01_discontinuousCounterexample_not_continuousOn`, directly from
  the metric epsilon-delta criterion at `1/2`. Thus the final conjunct is
  fully compiled. No statement defect was found; only the two power-law
  `MemLp` conversions remain.

  Going beyond hop 2, `apm_a92J01_p_exponent_lt_neg_one` and
  `apm_a92J01_neg_one_le_q_exponent` now prove the exact scalar thresholds
  shared by the sequence and real-line examples. Thus all reciprocal
  arithmetic is discharged: after rewriting the `p`th and `q`th norm powers,
  `Real.summable_nat_rpow` and `integrableOn_Ici_rpow_iff` receive their final
  hypotheses directly. The remaining bridge is solely the `MemLp` coercion,
  measurability, successor-index, and indicator conversions connecting the
  two concrete functions to those criteria. The frozen statement is unchanged.
  -/
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun p q _ hpq f hf => apm_a92J01_memLp_mono_on_unitMeasure p q hpq f hf
  · exact fun p q hq hpq => apm_a92J01_bridge_1 p q hq hpq
  · exact fun p q hq hpq => apm_a92J01_bridge_2 p q hq hpq
  · exact fun p _ => ⟨apm_a92J01_discontinuousCounterexample_memLp p,
      apm_a92J01_discontinuousCounterexample_not_continuousOn⟩
