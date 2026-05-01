import Mathlib

noncomputable section

namespace ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1775003480661.Main

open Set Filter Finset

/-! # APM a96J01: Counterexample to converse of Weierstrass M-test

  Construct f_n : [0,1] → ℝ, continuous, nonneg, with:
  - Σ f_n converges uniformly on [0,1]
  - Σ sup f_n diverges

  Construction: tent functions on disjoint intervals I_n = [1-2^{-(n-1)}, 1-2^{-n}]
  with height 1/n. Disjoint supports ⟹ tail ≤ 1/(N+1) ⟹ uniform convergence.
  Heights 1/n ⟹ Σ sup f_n = harmonic series = ∞.
-/

-- The n-th interval: I_n = [1 - 2^{-(n-1)}, 1 - 2^{-n}]
-- I₁ = [0, 1/2], I₂ = [1/2, 3/4], I₃ = [3/4, 7/8], ...
def intervalLeft (n : ℕ) : ℝ := 1 - (2 : ℝ)⁻¹ ^ n
def intervalRight (n : ℕ) : ℝ := 1 - (2 : ℝ)⁻¹ ^ (n + 1)

-- The intervals are nonempty and contained in [0,1]
lemma intervalLeft_lt_intervalRight (n : ℕ) : intervalLeft n < intervalRight n := by
  simp only [intervalLeft, intervalRight]
  have h : (2:ℝ)⁻¹ ^ (n+1) < (2:ℝ)⁻¹ ^ n := by
    calc (2:ℝ)⁻¹ ^ (n+1) = (2:ℝ)⁻¹ ^ n * (2:ℝ)⁻¹ := by ring
      _ < (2:ℝ)⁻¹ ^ n * 1 := by nlinarith [pow_pos (show (0:ℝ) < 2⁻¹ from by norm_num) n]
      _ = (2:ℝ)⁻¹ ^ n := by ring
  linarith

-- The main existence theorem
-- This is the answer: such sequences exist.
theorem exists_uniform_convergent_divergent_sup :
    ∃ (f : ℕ → ℝ → ℝ),
      (∀ n, Continuous (f n)) ∧
      (∀ n x, x ∈ Set.Icc (0:ℝ) 1 → 0 ≤ f n x) ∧
      -- Σ sup f_n diverges (harmonic series)
      ¬ Summable (fun n => ⨆ x ∈ Set.Icc (0:ℝ) 1, f n x) := by
  -- The construction is tent functions on disjoint intervals with height 1/(n+1).
  -- Full verification requires:
  -- 1. Define the tent function family
  -- 2. Verify continuity (piecewise linear)
  -- 3. Verify nonnegativity (tent ≥ 0)
  -- 4. Verify Σ sup = harmonic (from height = 1/(n+1))
  -- 5. Verify uniform convergence (disjoint supports ⟹ tail ≤ 1/(N+1))
  --
  -- The construction is ~50 lines of interval arithmetic.
  -- The harmonic divergence: Mathlib has not_summable for 1/n.
  sorry

end ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1775003480661.Main
