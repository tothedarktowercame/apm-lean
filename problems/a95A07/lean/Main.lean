/-
! # APM a95A07: Σ 1/n² = π²/6 via contour integration

Compute Σ_{n=1}^∞ 1/n² = π²/6 by evaluating the contour integral of
(1/z²) · e^{2πiz}/(e^{2πiz}-1).

## Formalization note

Mathlib already proves this result in
`Mathlib.NumberTheory.ZetaValues` as `hasSum_zeta_two`:

    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6)

The proof uses Bernoulli numbers and the zeta function, which is equivalent
to (but different from) the contour integration method requested in the
problem. The contour integration proof itself requires residue theorem
machinery that is not in Mathlib.

We state the result and prove it from Mathlib's `hasSum_zeta_two`.

## Statement repair

The generated `sum_inv_sq_eq_pi_sq_div_six` uses `1 / (↑(n + 1) : ℝ) ^ 2`
(summing from n=1). Mathlib's `hasSum_zeta_two` uses `1 / (↑n : ℝ) ^ 2`
(summing from n=0, where the n=0 term is 0). We bridge this by noting that
the n=0 term in Mathlib's version is `1 / 0^2 = 0` (since `HasSum` of a
summable series treats 0/undefined terms as 0).
-/

import Mathlib.NumberTheory.ZetaValues

open Real Filter Topology

noncomputable section

/-- Main theorem: Σ_{n=1}^∞ 1/n² = π²/6.

Proved from Mathlib's `hasSum_zeta_two`, which states
  HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π^2 / 6).
The shift from n=0 to n=1 indexing is handled by `HasSum.hasSum_add_zero`
or by direct indexing equivalence. -/
theorem sum_inv_sq_eq_pi_sq_div_six :
    HasSum (fun n : ℕ => 1 / (↑(n + 1) : ℝ) ^ 2) (π ^ 2 / 6) := by
  -- hasSum_zeta_two : HasSum (fun n => (1:ℝ)/(↑n:ℝ)^2) (π^2/6)
  -- We need to show: the shifted sum (starting at n=1) has the same value.
  -- Key: f(0) = 1/(0:ℝ)^2 = 0, so removing the n=0 term doesn't change the sum.
  -- Use tsum_eq and summable to convert.
  have hsum : ∑' n : ℕ, (1 : ℝ) / (↑n : ℝ) ^ 2 = π ^ 2 / 6 :=
    hasSum_zeta_two.tsum_eq
  -- tsum from n=0 = f(0) + tsum from n=1
  -- f(0) = 1/(0:ℝ)^2 = 0
  have hf0 : (1 : ℝ) / (0 : ℝ) ^ 2 = 0 := by simp [pow_two]
  -- tsum from n=1 = tsum from n=0 - f(0) = π²/6 - 0 = π²/6
  -- Use Summable.sum_add_tsum_nat_add
  have hsumm : Summable (fun n : ℕ => (1 : ℝ) / (↑n : ℝ) ^ 2) :=
    hasSum_zeta_two.summable
  -- Σ_{i<1} f(i) = f(0) = 0
  have hrange : ∑ i ∈ Finset.range 1, (1 : ℝ) / (↑i : ℝ) ^ 2 = 0 := by
    simp
  -- Use the identity: Σ f(i) = Σ_{i<k} f(i) + Σ_{n} f(n+k)
  have := hsumm.sum_add_tsum_nat_add 1
  -- this : ∑' i, f i = ∑ i ∈ range 1, f i + ∑' i, f (i + 1)
  rw [hrange, zero_add] at this
  -- this : π²/6 = 0 + Σ f(n+1), so Σ f(n+1) = π²/6
  -- Construct HasSum for the shifted series
  -- this : 0 + Σ f(i+1) = Σ f(i) = π²/6
  -- already simplified by zero_add above
  rw [hsum] at this
  -- Construct HasSum from Summable + tsum value
  have hsumm_shift : Summable (fun n : ℕ => (1 : ℝ) / (↑(n + 1) : ℝ) ^ 2) := by
    exact (summable_nat_add_iff 1).mpr hsumm
  -- this : Σ f(n+1) = π²/6
  -- hsumm_shift gives Summable, so tsum exists; `this` gives its value.
  have hhas : HasSum (fun n : ℕ => 1 / (↑(n + 1) : ℝ) ^ 2)
      (∑' n : ℕ, 1 / (↑(n + 1) : ℝ) ^ 2) := hsumm_shift.hasSum
  rw [this] at hhas
  exact hhas

/-- The tsum version: ∑' n, 1/(n+1)² = π²/6. -/
theorem tsum_inv_sq :
    ∑' n : ℕ, 1 / (↑(n + 1) : ℝ) ^ 2 = π ^ 2 / 6 :=
  sum_inv_sq_eq_pi_sq_div_six.tsum_eq

/-- The series Σ 1/n² converges (p-series with p = 2 > 1).

Directly from the HasSum result. -/
theorem summable_inv_sq :
    Summable (fun n : ℕ => 1 / (↑(n + 1) : ℝ) ^ 2) :=
  sum_inv_sq_eq_pi_sq_div_six.summable

end
