import Mathlib.Analysis.Calculus.Taylor

open Set

/-- If every positive-order derivative through `k` vanishes at the expansion
point, the order-`k` Taylor polynomial is the constant `g a`. -/
theorem taylorWithinEval_eq_value_of_iteratedDerivWithin_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) (s : Set ℝ) (a x : ℝ) (k : ℕ)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedDerivWithin i g s a = 0) :
    taylorWithinEval g k s a x = g a := by
  induction k with
  | zero => exact taylor_within_zero_eval g s a x
  | succ k ih =>
      rw [taylorWithinEval_succ, ih]
      · simp [hzero (k + 1) (by omega) (by omega)]
      · intro i hi hik
        exact hzero i hi (hik.trans (by omega))

/-- Global derivative vanishing supplies the interval-relative form used by
the Taylor polynomial whenever the interval is a unique-differentiability set. -/
theorem taylorWithinEval_eq_value_of_iteratedDeriv_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) (s : Set ℝ) (a x : ℝ) (k : ℕ)
    (hs : UniqueDiffOn ℝ s) (ha : a ∈ s) (hg : ContDiff ℝ k g)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedDeriv i g a = 0) :
    taylorWithinEval g k s a x = g a := by
  apply taylorWithinEval_eq_value_of_iteratedDerivWithin_eq_zero
  intro i hi hik
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (hg.contDiffAt.of_le (mod_cast hik)) ha]
  exact hzero i hi hik

#print axioms taylorWithinEval_eq_value_of_iteratedDerivWithin_eq_zero
#print axioms taylorWithinEval_eq_value_of_iteratedDeriv_eq_zero
