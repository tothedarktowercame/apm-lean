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

lemma apm_a99J05_summable_l1Norm_of_geometric_bound
    (f : ℕ → ℝ → ℝ)
    (hbound : ∀ n, apm_a99J05_l1Norm (f n) ≤ (2 : ℝ)⁻¹ ^ n) :
    Summable (fun n ↦ apm_a99J05_l1Norm (f n)) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact integral_nonneg (fun x ↦ norm_nonneg (f n x))
  · exact hbound
  · exact summable_geometric_of_norm_lt_one (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)

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
  /- CLOSER HOP 1 BOUNDARY.

  The helper above compiles the first decisive step of the second conjunct:
  geometric domination implies summability of the displayed `L¹` norms.
  Mathlib's proof of `MeasureTheory.integral_tsum` contains the next Tonelli
  step: finiteness of the sum of integrals of `‖f n x‖` implies that
  `∑' n, ‖f n x‖` is finite almost everywhere, hence `f n x → 0` almost
  everywhere. That implication is not exposed as a standalone theorem in this
  snapshot and still needs extraction with the ENNReal `lintegral` API.

  The first conjunct additionally requires a concrete typewriter sequence on
  `[0,1]`: integrable indicator spikes with measures tending to zero whose
  supports nevertheless hit almost every point infinitely often. Searches of
  `LEMMA-INDEX.md`, `ConstructionTargets`, solved probability/measure
  artifacts, Borel--Cantelli, and git history found no compiled enumeration of
  dyadic intervals or equivalent counterexample. Thus both the Tonelli
  extraction and the explicit moving-spike construction remain open. The
  frozen statement is unchanged.
  -/
  sorry
