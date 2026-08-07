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
  sorry
