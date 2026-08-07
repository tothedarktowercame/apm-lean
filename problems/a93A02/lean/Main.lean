import Mathlib

/-!
# APM a93A02 — L²-bounded a.e. convergence and convergence in Lᵖ

## Statement repairs

The source's finite supremum is encoded by a bound in `NNReal`; an `ENNReal`
bound could be `⊤` and would be vacuous. Sequences are indexed by `ℕ`, using
`n + 1` in the explicit spike family corresponding to the source's indexing
from one.

## Encoding questions

None. Both parts use the actual restricted Lebesgue measure and Mathlib's
`MemLp` and `eLpNorm`.

The counterexample follows the normalized-spike construction used in
`problems/a01J01/lean/Main.lean`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def apm_a93A02_measure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

def apm_a93A02_counterexample (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (n.succ : ℝ) *
    Set.indicator (Icc (0 : ℝ) ((n.succ : ℝ)⁻¹)) (fun _ ↦ (1 : ℝ)) x

theorem apm_a93a02 :
    (∀ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (p : ℝ≥0∞),
      (∀ n, MemLp (f n) 2 apm_a93A02_measure) →
      (∃ C : NNReal, ∀ n, eLpNorm (f n) 2 apm_a93A02_measure ≤ C) →
      (∀ᵐ x ∂apm_a93A02_measure,
        Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) →
      1 ≤ p → p < 2 →
      Tendsto
        (fun n ↦ eLpNorm (fun x ↦ f n x - g x) p apm_a93A02_measure)
        atTop (𝓝 0)) ∧
    (∀ n, MemLp (apm_a93A02_counterexample n) 2 apm_a93A02_measure) ∧
    (∀ n, eLpNorm (apm_a93A02_counterexample n) 2 apm_a93A02_measure ≤ 1) ∧
    (∀ᵐ x ∂apm_a93A02_measure,
      Tendsto (fun n ↦ apm_a93A02_counterexample n x) atTop (𝓝 0)) ∧
    ¬Tendsto
      (fun n ↦ eLpNorm (fun x ↦ apm_a93A02_counterexample n x - 0)
        2 apm_a93A02_measure)
      atTop (𝓝 0) := by
  sorry
