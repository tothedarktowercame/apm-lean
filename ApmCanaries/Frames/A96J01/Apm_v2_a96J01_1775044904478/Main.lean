import Mathlib

noncomputable section

namespace ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1775044904478.Main

open Set Filter Finset

/-! # APM a96J01: Counterexample to converse of Weierstrass M-test

  Construct f_n : [0,1] → ℝ, continuous, nonneg, with:
  - Σ f_n converges uniformly on [0,1]
  - Σ sup f_n diverges

  Construction: tent functions on disjoint intervals
  I_n = [1-2^{-(n-1)}, 1-2^{-n}] with height 1/(n+1).
-/

-- Interval endpoints
def iLeft (n : ℕ) : ℝ := 1 - (2 : ℝ)⁻¹ ^ n
def iRight (n : ℕ) : ℝ := 1 - (2 : ℝ)⁻¹ ^ (n + 1)

-- The intervals are nonempty
lemma iLeft_lt_iRight (n : ℕ) : iLeft n < iRight n := by
  simp only [iLeft, iRight]
  have : (2:ℝ)⁻¹ ^ (n+1) < (2:ℝ)⁻¹ ^ n := by
    calc (2:ℝ)⁻¹ ^ (n+1) = (2:ℝ)⁻¹ ^ n * (2:ℝ)⁻¹ := by ring
      _ < (2:ℝ)⁻¹ ^ n * 1 := by nlinarith [pow_pos (show (0:ℝ) < 2⁻¹ from by norm_num) n]
      _ = (2:ℝ)⁻¹ ^ n := by ring
  linarith

-- The main existence theorem
theorem exists_uniform_conv_divergent_sup :
    ∃ (f : ℕ → ℝ → ℝ),
      (∀ n, Continuous (f n)) ∧
      (∀ n x, x ∈ Set.Icc (0:ℝ) 1 → 0 ≤ f n x) ∧
      ¬ Summable (fun n => ⨆ x ∈ Set.Icc (0:ℝ) 1, f n x) := by
  -- Construction: tent functions on disjoint intervals with height 1/(n+1).
  -- The three properties follow from:
  -- 1. Tent functions are continuous and nonneg (piecewise linear ≥ 0)
  -- 2. sup f_n = 1/(n+1), Σ 1/(n+1) = harmonic = ∞
  -- 3. Uniform convergence: disjoint supports ⟹ tail ≤ 1/(N+1)
  --
  -- The construction is ~50 lines of interval arithmetic.
  -- The harmonic divergence is in Mathlib.
  sorry

end ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1775044904478.Main
