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
    -- Since (1:ℝ)/0^4 = 0 and (1:ℝ)/(k+1)^4 = (1:ℝ)/(k+1)^4, the two series are equal
    -- because they differ only at index 0 where both contribute 0.
    -- HasSum_iff_of_eventually_eq: if f =ᶠ[atTop] g then HasSum f a ↔ HasSum g a.
    have hkey : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 4) (Real.pi ^ 4 / 90) :=
      hasSum_zeta_four
    -- f(n) = 1/n^4 and g(k) = 1/(k+1)^4. These are NOT eventually equal.
    -- But: ∑' k, g(k) = ∑' n≥1, f(n) = ∑' n, f(n) - f(0) = π^4/90 - 0.
    -- Use HasSum.add_zero in reverse: HasSum g a ⟺ HasSum (fun n => if n=0 then 0 else g(n-1)) a
    -- Actually: just directly compute the tsum.
    -- Key: fun k => 1/(k+1)^4 is the same as fun n => if n = 0 then 0 else 1/n^4
    -- because at n=0: 1/0^4 = 0, at n=k+1≥1: 1/n^4 = 1/(k+1)^4.
    -- No wait, these have different indices. fun k => 1/(k+1)^4 at k=0 gives 1/1 = 1.
    -- fun n => 1/n^4 at n=0 gives 0, at n=1 gives 1.
    -- So ∑' k, 1/(k+1)^4 = ∑'_{n=1}^∞ 1/n^4 = ∑' n, 1/n^4 - 1/0^4 = π^4/90 - 0 = π^4/90.
    -- Need: ∑' k, f(k+1) = ∑' n, f(n) - f(0) when f(0) = 0.
    -- This is just ∑' k, f(k+1) = ∑' n, f(n) since f(0) = 0.
    -- Use HasSum.comp_injective with Nat.succ_injective? No, that requires the
    -- function to be on the codomain of the injection.
    -- Actually the cleanest: use tsum_eq and just verify numerically.
    rw [← hkey.tsum_eq]
    -- Need: ∑' k, 1/(k+1)^4 = ∑' n, 1/n^4
    -- Boundary (closer hop 2): the shift lemma ∑' k, f(k+1) = ∑' n, f(n) when f(0)=0.
    -- `Finset.sum_range_succ` gives ∑_{n∈range(N+1)} f(n) = ∑_{n∈range N} f(n) + f(N),
    -- not the decomposition at 0 that we need.
    -- The correct identity is: ∑_{n∈range(N+1)} f(n) = f(0) + ∑_{k∈range N} f(k+1),
    -- which follows from range(N+1) = {0} ∪ {k+1 : k ∈ range N}.
    -- Since f(0)=0: ∑_{n∈range(N+1)} f(n) = ∑_{k∈range N} f(k+1).
    -- As N→∞: ∑' f(n) = ∑' f(k+1). Both converge.
    -- Assembly: need `Finset.sum_range_succ'` or manual range decomposition.
    -- The lemma doesn't exist in this exact form in Mathlib.
    sorry
  exact hshift

#print axioms apm_aunk03
