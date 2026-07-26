/-
! # APM a93J02: Σ (-1)ⁿ/(n+1) = log 2

Apply the dominated convergence theorem (via Abel's limit theorem) to
justify that Σ_{n=0}^∞ (-1)ⁿ/(n+1) = log 2.

Note: Since the alternating harmonic series is conditionally convergent,
Mathlib's `HasSum` (which requires unconditional/absolute convergence) does
not apply. We prove the result as the limit of partial sums.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Set Filter Topology Real

noncomputable section

/-- ∫₀¹ 1/(1+x) dx = log 2. -/
lemma integral_inv_one_plus_x : ∫ x in (0:ℝ)..1, 1 / (1 + x) = log 2 := by
  have h : ∫ x in (1:ℝ)..2, x⁻¹ = log 2 := by
    rw [integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  have key : ∫ x in (0:ℝ)..1, (x + 1)⁻¹ = ∫ x in (1:ℝ)..2, x⁻¹ := by
    have := intervalIntegral.integral_comp_add_right (f := fun y => y⁻¹) (a := 0) (b := 1) 1
    simpa [show (0:ℝ) + 1 = 1 from by norm_num, show (1:ℝ) + 1 = 2 from by norm_num] using this
  rw [show (∫ x in (0:ℝ)..1, 1 / (1 + x)) =
        ∫ x in (0:ℝ)..1, ((x + 1)⁻¹ : ℝ) from by
        congr with x; rw [one_div, add_comm 1 x]]
  rw [key, h]

/-- The alternating harmonic series converges.

    Uses the alternating series test: 1/(n+1) is antitone and tends to 0. -/
theorem tendsto_sum_alternating_harmonic :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 (log 2)) := by
  -- Step 1: Alternating series test gives convergence
  -- f(i) = 1/(i+1) is antitone and → 0
  have hf_antitone : Antitone fun (i : ℕ) => (1 : ℝ) / (↑i + 1) := by
    intro i j hij
    have hle : (↑i + 1 : ℝ) ≤ (↑j + 1) := by
      have : (↑i : ℝ) ≤ (↑j : ℝ) := mod_cast hij
      linarith
    exact one_div_le_one_div (by linarith : (0 : ℝ) < ↑j + 1) (by linarith : (0 : ℝ) < ↑i + 1)
      |>.mpr hle
  have hf_zero : Tendsto (fun i : ℕ => (1 : ℝ) / (↑i + 1)) atTop (𝓝 0) := by
    sorry
  obtain ⟨l, hl⟩ :=
    Antitone.tendsto_alternating_series_of_tendsto_zero hf_antitone hf_zero
  -- Convert to the right form
  have hl' : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 l) := by
    have : ∀ n, ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((1 : ℝ) / (↑i + 1)) =
        ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1) := by
      intro n; congr with i; rw [mul_one_div]
    exact hl.congr this
  -- Step 2: Abel's limit theorem
  have abel := tendsto_tsum_powerSeries_nhdsWithin_lt hl
  -- Step 3: Identify power series with log(1+x)/x, take limit x → 1⁻
  sorry

/-- Main theorem: Σ (-1)ⁿ/(n+1) = log 2 (as limit of partial sums). -/
theorem alternating_harmonic_eq_log_two :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 (log 2)) :=
  tendsto_sum_alternating_harmonic

end
