import Mathlib

/-!
# APM a99J05 — small L¹ norm versus almost-everywhere convergence

## Statement repairs

None. Sequences are indexed by `ℕ`; this is the standard Lean reindexing of
the source's sequence beginning at one.

## Encoding questions

None. The functions, restricted Lebesgue measure on `[0,1]`, L¹ norms, and
almost-everywhere pointwise convergence are all represented directly.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def apm_a99J05_measure : Measure ℝ := volume.restrict (Set.Icc 0 1)

def apm_a99J05_l1Norm (f : ℝ → ℝ) : ℝ :=
  ∫ x, ‖f x‖ ∂apm_a99J05_measure

theorem apm_a99j05 :
    (∃ f : ℕ → ℝ → ℝ,
      (∀ n, Integrable (f n) apm_a99J05_measure) ∧
      Tendsto (fun n ↦ apm_a99J05_l1Norm (f n)) atTop (𝓝 0) ∧
      ¬(∀ᵐ x ∂apm_a99J05_measure,
        ∃ a : ℝ, Tendsto (fun n ↦ f n x) atTop (𝓝 a))) ∧
    (∀ f : ℕ → ℝ → ℝ,
      (∀ n, Integrable (f n) apm_a99J05_measure) →
      (∀ n, apm_a99J05_l1Norm (f n) ≤ (2 : ℝ)⁻¹ ^ n) →
      ∀ᵐ x ∂apm_a99J05_measure,
        Tendsto (fun n ↦ f n x) atTop (𝓝 0)) := by
  sorry
