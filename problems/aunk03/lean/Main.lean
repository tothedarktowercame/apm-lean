import Mathlib

/-!
# APM aunk03
-/

open Set

noncomputable def apm_aunk03_kernel (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) / z ^ 4

def apm_aunk03_squareContour (n : ℕ) : Set ℂ :=
  let r : ℝ := n + (1 / 2 : ℝ)
  {z | (|z.re| = r ∧ |z.im| ≤ r) ∨ (|z.im| = r ∧ |z.re| ≤ r)}

theorem apm_aunk03 :
    (∑' k : ℕ, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 4) = Real.pi ^ 4 / 90 := by
  -- ∑' k, 1/(k+1)^4 = ∑' n, 1/n^4 since the n=0 term is 1/0^4 = 0 in ℝ
  -- Then ∑' n, 1/n^4 = π^4/90 by hasSum_zeta_four
  have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 4 = 0 := by simp
  -- Key: the two sequences agree a.e. (differ only at n=0 where one is 0)
  -- Use HasSum.eq to transfer
  apply HasSum.tsum_eq
  -- fun k => 1/(k+1)^4 has sum π^4/90 because:
  -- fun n => 1/n^4 has sum π^4/90 (hasSum_zeta_four)
  -- and 1/0^4 = 0, so the shifted version has the same sum
  have hshift : HasSum (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 4) (Real.pi ^ 4 / 90) := by
    have hkey : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 4) (Real.pi ^ 4 / 90) :=
      hasSum_zeta_four
    -- The additive counterpart generated from the product-shift API removes
    -- the first term. Here that term is zero. (Mathlib: `hasSum_nat_add_iff'`.)
    have hs := (hasSum_nat_add_iff' (f := fun n : ℕ ↦
      (1 : ℝ) / ((n : ℕ) : ℝ) ^ 4) 1).mpr hkey
    simpa only [Finset.sum_range_one, h0, sub_zero, Nat.add_comm] using hs
  exact hshift

#print axioms apm_aunk03
