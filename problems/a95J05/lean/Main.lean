/-
! # APM a95J05: Convergence in measure iff ∫|arctan fₙ| → 0

On a finite measure space (Ω, μ), fₙ → 0 in measure iff
∫|arctan fₙ| dμ → 0.

## Proof strategy

(⟹) Convergence in measure ⟹ ∫|arctan fₙ| → 0:
  Split: ∫|arctan fₙ| ≤ arctan(δ)·μ(Ω) + (π/2)·μ({|fₙ|>δ}).
  Choose δ small (first term < ε/2), then N large (second term < ε/2).

(⟸) ∫|arctan fₙ| → 0 ⟹ convergence in measure:
  μ({|fₙ|>ε}) ≤ ∫|arctan fₙ| / arctan(ε) → 0 (Markov-type bound).

## Proved lemmas

- arctan_zero, arctan_pos, abs_arctan_lt are direct from Mathlib.
- The Markov bound and splitting require measure theory assembly.

## Statement repair

The generated `abs_arctan_lt_pi_div_two` uses `<`; we use `≤` since
Mathlib has `arctan_lt_pi_div_two` (strict) and the negation gives
|arctan t| ≤ π/2 trivially. For the integral bound, ≤ suffices.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open MeasureTheory Filter Real Topology

open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Convergence in measure: μ({|fₙ| > ε}) → 0 for all ε > 0. -/
def TendstoInMeasureZero (f : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ {x | ε < |f n x|}) atTop (𝓝 0)

/-- arctan(0) = 0. -/
lemma arctan_zero' : arctan 0 = 0 := arctan_zero

/-- arctan(t) > 0 for t > 0 (strictly monotone arctan). -/
lemma arctan_pos' {t : ℝ} (ht : 0 < t) : 0 < arctan t :=
  arctan_pos.mpr ht

/-- |arctan(t)| < π/2 for all t. -/
lemma abs_arctan_lt (t : ℝ) : |arctan t| < π / 2 := by
  refine abs_lt.mpr ⟨?_, ?_⟩
  · have h1 : -(π/2) < arctan t := by
      have : arctan (-t) < π/2 := arctan_lt_pi_div_two (-t)
      rw [arctan_neg] at this
      linarith
    exact h1
  · exact arctan_lt_pi_div_two t

/-- (⟸) ∫|arctan fₙ| → 0 ⟹ convergence in measure.

**Blocker:** The Markov-type bound
  μ({|f| > ε}) ≤ ∫|arctan f| / arctan(ε)
requires splitting the integral over {|f| > ε} and {|f| ≤ ε},
using that |arctan(t)| ≥ arctan(ε) > 0 when |t| > ε. This needs
`set_integral_le_integral` and measurability setup. -/
theorem tendstoInMeasure_of_integral_arctan_tendsto
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hint : Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0)) :
    TendstoInMeasureZero f μ := by
  sorry

/-- (⟹) Convergence in measure implies ∫|arctan fₙ| → 0.

**Blocker:** The splitting bound
  ∫|arctan fₙ| ≤ arctan(δ)·μ(Ω) + (π/2)·μ({|fₙ| > δ})
requires `integral_add_compl` (or set integral decomposition) and
the bound |arctan fₙ| ≤ π/2. -/
theorem integral_arctan_tendsto_of_tendstoInMeasure
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hconv : TendstoInMeasureZero f μ) :
    Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0) := by
  sorry

/-- Main theorem: equivalence of convergence in measure and integral of arctan. -/
theorem tendstoInMeasure_iff_integral_arctan
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) :
    TendstoInMeasureZero f μ ↔
      Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0) :=
  ⟨integral_arctan_tendsto_of_tendstoInMeasure hf,
   tendstoInMeasure_of_integral_arctan_tendsto hf⟩

end
