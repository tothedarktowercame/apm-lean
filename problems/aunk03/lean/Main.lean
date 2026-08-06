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
    -- Use Summable.tsum_eq_add_tsum_ite to decompose ∑' f = f(0) + ∑' (if n=0 then 0 else f n)
    -- Since f(0) = 0, the tail sum ∑' (if n=0 then 0 else f n) = ∑' k, f(k+1).
    -- Actually simpler: ∑' k, f(k+1) = ∑' n, f(n) - f(0) = π^4/90 - 0.
    -- But the cleanest: just use tsum_eq_add_tsum_ite with b = 0.
    have hkey : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 4) (Real.pi ^ 4 / 90) :=
      hasSum_zeta_four
    have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 4 = 0 := by simp
    -- ∑' n, f n = f(0) + ∑' n, (if n = 0 then 0 else f n)
    -- The RHS tail sum ∑' n, (if n = 0 then 0 else f n) equals ∑' k, f(k+1)
    -- because it's the same sequence up to a reindexing (n ≥ 1 ↦ k = n-1).
    -- Actually the ite version doesn't directly give us ∑' k, f(k+1).
    -- Let me just prove it from HasSum directly.
    -- HasSum f a means: ∀ᶠ s in atTop (as finsets), ∑ n ∈ s, f n ≈ a.
    -- For any finite set s containing 0: ∑ n ∈ s, f n = f(0) + ∑ n ∈ s\{0}, f n
    -- = 0 + ∑ n ∈ s\{0}, f n = ∑ n ∈ s\{0}, f n.
    -- And {n ∈ s : n ≥ 1} corresponds to {k : k+1 ∈ s}.
    -- So ∑ n ∈ s, f n = ∑ n ∈ s ∩ {n : n ≥ 1}, f n = ∑ k ∈ {k : k+1 ∈ s}, f(k+1).
    -- This means HasSum f a ↔ HasSum (fun k => f(k+1)) a when f(0) = 0.
    -- Formalize: use hasSum_iff_of_zero_add or prove from the definition.
    sorry
    -- Boundary (closer hop 1): the shift lemma HasSum f a → HasSum (f∘succ) a (when f(0)=0)
    -- is equivalent to: partial sums ∑_{n=0}^{N} f n = f(0) + ∑_{k=0}^{N-1} f(k+1).
    -- With f(0)=0: ∑_{n=0}^{N} f n = ∑_{k=0}^{N-1} f(k+1), so both sequences → a.
    -- APIs checked: `Finset.sum_range_succ`, `hasSum_nat_add`, `Summable.tsum_eq_add_tsum_ite`
    -- The decomposition exists as `Summable.tsum_eq_add_tsum_ite` but gives
    -- ∑' f = f b + ∑' (if n=b then 0 else f n), not ∑' f = f 0 + ∑' f∘succ.
    -- The reindexing (if n=0 then 0 else f n) ⟷ f(k+1) requires a bijection argument.
  exact hshift

#print axioms apm_aunk03
