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
  CLOSER HOP 1: the first conjunct is now closed by the compiled helper
  `apm_a92J01_memLp_mono_on_unitMeasure`, using Mathlib's
  `MemLp.mono_exponent` and the existing finite-measure instance for
  `volume.restrict (Icc 0 1)`.

  Searches of the p-series, `memLp_norm_rpow_iff`, counting-measure, and
  interval-integrability APIs found all scalar ingredients for the two
  power-law counterexamples, but no packaged equivalence reducing these exact
  real-exponent `MemLp` goals to `Real.summable_nat_rpow` and
  `integrableOn_Ici_rpow_iff`.  Those coercion and measurability conversions
  remain the main bridge.  The compiled helper
  `apm_a92J01_discontinuousCounterexample_memLp` also closes the membership
  half of the last conjunct through `memLp_indicator_const`; only the
  one-sided discontinuity argument at `1/2` remains there. No statement defect
  was found.
  -/
  sorry
