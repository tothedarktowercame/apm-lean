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
  CLOSER HOPS 1--2: the first conjunct is now closed by the compiled helper
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
  -/
  sorry
