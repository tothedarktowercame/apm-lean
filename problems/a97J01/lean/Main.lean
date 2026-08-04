/-
! # APM a97J01: Bounded integrals over bounded pieces force global integrability

Let f: ℝ → ℝ be Lebesgue measurable. Assume ∃ c > 0 such that for every
bounded measurable set A on which f is bounded, |∫_A f dm| ≤ c.
Prove that f ∈ L¹(ℝ), i.e. ∫_ℝ |f| dm ≤ 2c.

## Note on the statement

The problem.tex says "Prove that f is Lebesgue measurable", but f is already
assumed measurable — this is circular. The intended conclusion (standard for
this UT-Austin prelim) is that f is Lebesgue **integrable**, with the bound
∫|f| ≤ 2c. We prove exactly that.

## Strategy (from informal-solution.md)

1. Split f = f⁺ - f⁻ where f⁺ = max(f,0), f⁻ = max(-f,0).
2. For each n, define A_n = {|x| ≤ n, 0 ≤ f ≤ n}. Apply hypothesis: ∫_{A_n} f ≤ c.
   Since f ≥ 0 on A_n, ∫_{A_n} f⁺ ≤ c.
3. A_n ↑ {f ≥ 0}, so by MCT, ∫ f⁺ = lim ∫_{A_n} f⁺ ≤ c.
4. Symmetrically ∫ f⁻ ≤ c.
5. ∫|f| = ∫f⁺ + ∫f⁻ ≤ 2c.

## Phase-A hints used
-- (Memory: math-informal/monotone-approximation) MCT is the core passage from per-n bounds to the limit.
-- (Memory: math-informal/exhaustion-as-theorem) the A_n, B_n exhaustion is the structural technique.

## Phase-A hints dropped
- #3 (finite interval measure): not needed; we use ENNReal-level arguments.

## Boundary: remaining MCT bridge

The core setup is proved: truncated sets A_n, B_n are defined, the hypothesis
is applied to each, and per-n integral bounds are established (∫_{A_n} f ≤ c
and ∫_{B_n} f ≥ -c). The remaining bridge is:

1. Connecting the Bochner set integral ∫_{A_n} f to the lintegral
   ∫⁻_{A_n} ENNReal.ofReal(f). The API `ofReal_integral_eq_lintegral_ofReal`
   requires `Integrable f (μ.restrict s)`, which requires proving f has finite
   integral on each A_n (bounded on bounded set → integrable).

2. Applying `lintegral_iSup_ae` (MCT) to pass from per-n bounds to the global
   lintegral bound ∫⁻ ENNReal.ofReal(f⁺) ≤ c.

3. The symmetric argument for f⁻ and the final combination.

APIs searched:
- `lintegral_indicator` — FOUND: ∫⁻ indicator · f = ∫⁻_{s} f
- `ofReal_integral_eq_lintegral_ofReal` — FOUND: connects Bochner and lintegral
  for nonneg integrable functions
- `integral_eq_lintegral_of_nonneg_ae` — FOUND: alternative connection
- `lintegral_iSup_ae` — FOUND: MCT in iSup form
- `lintegral_tendsto_of_tendsto_of_monotone` — FOUND: MCT in limit form

Routes tried:
- Direct use of `ofReal_integral_eq_lintegral_ofReal` — requires proving
  Integrable f (volume.restrict (A n)), which requires HasFiniteIntervalIntegral
  or equivalent integrability on bounded sets. The integrability proof on A_n
  (f bounded by n, A_n finite measure) requires assembling several Mathlib API
  pieces that don't compose smoothly.

Routes NOT investigated:
- Defining the approximating sequence and applying `lintegral_tendsto_of_tendsto_of_monotone`
  directly (requires building monotone sequence + pointwise convergence)
- Using `MeasureTheory.SimpleFunc` approximation
- Working entirely in the L1/AEEqFun framework
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Filter Set
open scoped ENNReal

namespace APMa97J01

/-- Main theorem: under the bounded-integral hypothesis, f is integrable with ∫|f| ≤ 2c.

    Note: problem.tex says "prove f is measurable" which is circular since measurability
    is assumed. The intended conclusion is integrability, with ∫|f| ≤ 2c.

    The proof uses the exhaustion technique: define truncated sets A_n = {|x|≤n, 0≤f≤n}
    and B_n = {|x|≤n, -n≤f≤0}, apply the hypothesis to each, then pass to the limit
    via the Monotone Convergence Theorem.

    -- (Memory: math-informal/monotone-approximation) MCT passes per-n bounds to the limit.
    -- (Memory: math-informal/exhaustion-as-theorem) the A_n, B_n sets exhaust {f ≥ 0} and {f ≤ 0}. -/
theorem bounded_integral_implies_integrable
    (f : ℝ → ℝ)
    (hf_meas : Measurable f)
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ (A : Set ℝ), MeasurableSet A → Bornology.IsBounded A →
      (∃ M, ∀ x ∈ A, |f x| ≤ M) →
      |∫ x in A, f x ∂volume| ≤ c) :
    Integrable f volume ∧ ∫⁻ x, ENNReal.ofReal |f x| ∂volume ≤ ENNReal.ofReal (2 * c) := by
  -- Step 1: Define A_n = {|x| ≤ n, 0 ≤ f ≤ n}
  let A := fun (n : ℕ) => (Icc (-n : ℝ) n) ∩ {x | 0 ≤ f x} ∩ {x | f x ≤ n}

  have hA_meas : ∀ n : ℕ, MeasurableSet (A n) := fun n => by
    refine measurableSet_Icc.inter ?_ |>.inter ?_
    · exact hf_meas measurableSet_Ici
    · exact hf_meas measurableSet_Iic
  have hA_bounded : ∀ n : ℕ, Bornology.IsBounded (A n) := fun n =>
    Bornology.IsBounded.subset (Metric.isBounded_Icc (-(n:ℝ)) n) fun x hx => by
      simp only [A] at hx; exact hx.1.1
  have hA_fbounded : ∀ n : ℕ, ∃ M, ∀ x ∈ A n, |f x| ≤ M := fun n => by
    refine ⟨n, fun x hx => ?_⟩
    show |f x| ≤ n
    have hf : 0 ≤ f x ∧ f x ≤ (n : ℝ) := by
      show _ ∧ _
      simp only [A] at hx
      exact ⟨hx.1.2, hx.2⟩
    exact abs_le.mpr ⟨by linarith [hf.1], mod_cast hf.2⟩

  -- Step 2: Apply the hypothesis to each A_n: |∫_{A_n} f| ≤ c
  have hA_int_bound : ∀ n : ℕ, |∫ x in A n, f x ∂volume| ≤ c := fun n =>
    hbound (A n) (hA_meas n) (hA_bounded n) (hA_fbounded n)

  -- Step 3: On A_n, f ≥ 0, so ∫_{A_n} f ≥ 0, thus ∫_{A_n} f ≤ c
  have hA_int_nonneg : ∀ n : ℕ, 0 ≤ ∫ x in A n, f x ∂volume := fun n => by
    apply setIntegral_nonneg (hA_meas n)
    intro x hx
    show 0 ≤ f x
    simp only [A] at hx
    exact hx.1.2
  have hA_int_le : ∀ n : ℕ, ∫ x in A n, f x ∂volume ≤ c := fun n => by
    have hn := hA_int_nonneg n
    have hb := hA_int_bound n
    exact (abs_of_nonneg hn).symm ▸ hb

  -- Step 4: Define B_n = {|x| ≤ n, -n ≤ f ≤ 0} (the negative part truncation)
  let B := fun (n : ℕ) => (Icc (-n : ℝ) n) ∩ {x | -n ≤ f x} ∩ {x | f x ≤ 0}
  have hB_meas : ∀ n : ℕ, MeasurableSet (B n) := fun n => by
    refine measurableSet_Icc.inter ?_ |>.inter ?_
    · exact hf_meas measurableSet_Ici
    · exact hf_meas measurableSet_Iic
  have hB_bounded : ∀ n : ℕ, Bornology.IsBounded (B n) := fun n =>
    Bornology.IsBounded.subset (Metric.isBounded_Icc (-(n:ℝ)) n) fun x hx => by
      simp only [B] at hx; exact hx.1.1
  have hB_fbounded : ∀ n : ℕ, ∃ M, ∀ x ∈ B n, |f x| ≤ M := fun n => by
    refine ⟨n, fun x hx => ?_⟩
    show |f x| ≤ n
    have hf : -(n:ℝ) ≤ f x ∧ f x ≤ 0 := by
      simp only [B] at hx; exact ⟨hx.1.2, hx.2⟩
    exact abs_le.mpr ⟨mod_cast hf.1, by linarith [hf.2]⟩
  have hB_int_bound : ∀ n : ℕ, |∫ x in B n, f x ∂volume| ≤ c := fun n =>
    hbound (B n) (hB_meas n) (hB_bounded n) (hB_fbounded n)
  have hB_int_nonpos : ∀ n : ℕ, ∫ x in B n, f x ∂volume ≤ 0 := fun n => by
    apply setIntegral_nonpos (hB_meas n)
    intro x hx
    show f x ≤ 0
    simp only [B] at hx; exact hx.2
  have hB_int_ge_neg_c : ∀ n : ℕ, -c ≤ ∫ x in B n, f x ∂volume := fun n => by
    have hb := hB_int_bound n
    have hn := hB_int_nonpos n
    have : |∫ x in B n, f x ∂volume| = -(∫ x in B n, f x ∂volume) := by
      rw [abs_of_nonpos hn]
    rw [this] at hb
    linarith

  -- Step 5: Bounded lintegral of positive part via MCT
  -- f⁺ = max(f,0), and on A_n, f⁺ = f. The per-n Bochner integral bound ∫_{A_n} f ≤ c
  -- must be transported to the lintegral level to apply MCT.
  -- Boundary: see file-level comment for the remaining bridge.
  have hlint_pos : ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂volume ≤ ENNReal.ofReal c := by
    sorry

  -- Step 6: Bounded lintegral of negative part via MCT (symmetric)
  have hlint_neg : ∫⁻ x, ENNReal.ofReal (max (-f x) 0) ∂volume ≤ ENNReal.ofReal c := by
    sorry

  -- Step 7: Combine
  -- |f| = f⁺ + f⁻, so ∫⁻ ofReal|f| = ∫⁻ ofReal(f⁺) + ∫⁻ ofReal(f⁻) ≤ 2c
  have hlint_abs : ∫⁻ x, ENNReal.ofReal |f x| ∂volume ≤ ENNReal.ofReal (2 * c) := by
    sorry

  -- Step 8: Conclude integrability from finite lintegral
  refine ⟨?_, hlint_abs⟩
  sorry

#print axioms APMa97J01.bounded_integral_implies_integrable

end APMa97J01
