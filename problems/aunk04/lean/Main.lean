import Mathlib
import ConstructionTargets.Rouche

/-!
# APM aunk04 — Rouché zero count and polynomial growth of entire functions

## Statement repairs

In part (a), the source writes `f(x)` while defining a complex polynomial in
the variable `z`.  This is treated as the typographical correction `f(z)`.

## Encoding notes

The zero count uses the polynomial's root multiset, so multiplicities are
retained.  In part (b), the degree conclusion is stated without a floor
operation: every coefficient with natural index `k > m` vanishes.  This is the
direct coefficient form of `degree ≤ floor(m)`.
-/

open Set MeasureTheory Filter
open scoped Topology
open scoped Polynomial

noncomputable def apm_aunk04_polynomial : ℂ[X] :=
  Polynomial.X ^ 4 - Polynomial.C 3 * Polynomial.X ^ 3 +
    Polynomial.X ^ 2 + Polynomial.C 6

noncomputable def apm_aunk04_remainder : ℂ[X] :=
  Polynomial.X ^ 4 - Polynomial.C 3 * Polynomial.X ^ 3 + Polynomial.X ^ 2

/-- On the unit circle, the nonconstant part has norm at most five, strictly
less than the norm of the constant term six. -/
lemma apm_aunk04_rouche_bound (z : ℂ) (hz : ‖z‖ = 1) :
    ‖Polynomial.eval z apm_aunk04_remainder‖ <
      ‖Polynomial.eval z (Polynomial.C 6 : ℂ[X])‖ := by
  have htri : ‖z ^ 4 - 3 * z ^ 3 + z ^ 2‖ ≤
      ‖z ^ 4‖ + ‖3 * z ^ 3‖ + ‖z ^ 2‖ := by
    calc
      ‖z ^ 4 - 3 * z ^ 3 + z ^ 2‖
          ≤ ‖z ^ 4 - 3 * z ^ 3‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ (‖z ^ 4‖ + ‖3 * z ^ 3‖) + ‖z ^ 2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
  simp [apm_aunk04_remainder, hz] at htri ⊢
  exact lt_of_le_of_lt htri (by norm_num)

/-- The polynomial has no roots in the open unit disk.  For this particular
polynomial the constant comparison in Rouché can be discharged directly. -/
lemma apm_aunk04_no_roots_in_unitDisk :
    (apm_aunk04_polynomial.roots.filter (fun z => ‖z‖ < 1)).card = 0 := by
  classical
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro z hzroot
  have hpoly_ne : apm_aunk04_polynomial ≠ 0 := by
    intro hzero
    have := congrArg (fun q : ℂ[X] => q.coeff 0) hzero
    norm_num [apm_aunk04_polynomial] at this
  have heval : Polynomial.eval z apm_aunk04_polynomial = 0 :=
    Polynomial.isRoot_of_mem_roots hzroot
  have hrem : Polynomial.eval z apm_aunk04_remainder = -(6 : ℂ) := by
    simp [apm_aunk04_polynomial, apm_aunk04_remainder] at heval ⊢
    linear_combination heval
  intro hz
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hzle : ‖z‖ ≤ 1 := le_of_lt hz
  have htri : ‖z ^ 4 - 3 * z ^ 3 + z ^ 2‖ ≤
      ‖z‖ ^ 4 + 3 * ‖z‖ ^ 3 + ‖z‖ ^ 2 := by
    calc
      ‖z ^ 4 - 3 * z ^ 3 + z ^ 2‖
          ≤ ‖z ^ 4 - 3 * z ^ 3‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ (‖z ^ 4‖ + ‖3 * z ^ 3‖) + ‖z ^ 2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖z‖ ^ 4 + 3 * ‖z‖ ^ 3 + ‖z‖ ^ 2 := by simp
  have h2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  have h3 : ‖z‖ ^ 3 ≤ 1 := by
    calc
      ‖z‖ ^ 3 = ‖z‖ ^ 2 * ‖z‖ := by ring
      _ ≤ 1 * 1 := mul_le_mul h2 hzle hz0 zero_le_one
      _ = 1 := one_mul 1
  have h4 : ‖z‖ ^ 4 ≤ 1 := by
    calc
      ‖z‖ ^ 4 = ‖z‖ ^ 2 * ‖z‖ ^ 2 := by ring
      _ ≤ 1 * 1 := mul_le_mul h2 h2 (sq_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hsmall : ‖Polynomial.eval z apm_aunk04_remainder‖ < 6 := by
    simp [apm_aunk04_remainder]
    exact lt_of_le_of_lt htri (by nlinarith)
  rw [hrem, norm_neg] at hsmall
  norm_num at hsmall

/-- Cauchy's estimate at an arbitrary positive radius, with the polynomial
growth hypothesis substituted on the boundary sphere. -/
lemma apm_aunk04_growth_cauchy_bound
    (f : ℂ → ℂ) (A B m : ℝ)
    (hf : Differentiable ℂ f)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A + B * Real.rpow ‖z‖ m)
    (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ‖iteratedDeriv k f 0‖ ≤
      k.factorial * (A + B * Real.rpow R m) / R ^ k := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR
    hf.diffContOnCl
  intro z hz
  have hnorm : ‖z‖ = R := by
    exact mem_sphere_zero_iff_norm.mp hz
  simpa [hnorm] using hgrowth z

/-- Why this unblocks `apm_aunk04`: this is the exact scalar-asymptotic
consequence of the compiled arbitrary-radius Cauchy estimate. It eliminates
every Taylor coefficient whose natural order strictly exceeds the real growth
exponent. -/
theorem apm_aunk04_bridge_1
    (f : ℂ → ℂ) (A B m : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hm : 0 < m)
    (hf : Differentiable ℂ f)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A + B * Real.rpow ‖z‖ m) :
    ∀ k : ℕ, m < k → iteratedDeriv k f 0 = 0 := by
  intro k hk
  by_contra hne
  have hpos : 0 < ‖iteratedDeriv k f 0‖ := by
    rw [norm_pos_iff]; exact hne
  have hkm : (m : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkp : (0 : ℝ) < (k : ℝ) := lt_trans hm hkm
  have hpow : Tendsto (fun R : ℝ => Real.rpow R m / R ^ k) atTop (𝓝 0) := by
    have heq : (fun R : ℝ => Real.rpow R m / R ^ k) =ᶠ[atTop]
        fun R : ℝ => R ^ (m - (k : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      rw [← Real.rpow_natCast R k, Real.rpow_sub hR]
      rfl
    have htend : Tendsto (fun R : ℝ => R ^ (m - (k : ℝ))) atTop (𝓝 0) := by
      have hminus : m - (k : ℝ) = -((k : ℝ) - m) := by ring
      rw [hminus]
      exact tendsto_rpow_neg_atTop (by linarith)
    exact Tendsto.congr' heq.symm htend
  have hden : Tendsto (fun R : ℝ => A / R ^ k) atTop (𝓝 0) := by
    have heq : (fun R : ℝ => A / R ^ k) =ᶠ[atTop]
        fun R : ℝ => A * R ^ (-(k : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      rw [← Real.rpow_natCast R k, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hR)]
    simpa using Tendsto.congr' heq.symm (Tendsto.const_mul A (tendsto_rpow_neg_atTop hkp))
  have hlim : Tendsto (fun R : ℝ =>
      (k.factorial : ℝ) * (A + B * Real.rpow R m) / R ^ k) atTop (𝓝 0) := by
    have heq : (fun R : ℝ =>
        (k.factorial : ℝ) * (A + B * Real.rpow R m) / R ^ k) =ᶠ[atTop]
        fun R : ℝ => (k.factorial : ℝ) * (A / R ^ k + B * (Real.rpow R m / R ^ k)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      field_simp [ne_of_gt hR]
    refine Tendsto.congr' heq.symm ?_
    simpa using Tendsto.const_mul (k.factorial : ℝ)
      (hden.add (Tendsto.const_mul B hpow))
  obtain ⟨R, hlt, hR0⟩ :=
    ((hlim.eventually (gt_mem_nhds hpos)).and (eventually_gt_atTop (0 : ℝ))).exists
  have hb := apm_aunk04_growth_cauchy_bound f A B m hf hgrowth k hR0
  linarith
theorem apm_aunk04_bridge_2
    (f : ℂ → ℂ) (m : ℝ) (hf : Differentiable ℂ f)
    (hvanish : ∀ k : ℕ, m < k → iteratedDeriv k f 0 = 0) :
    ∃ p : ℂ[X],
      (∀ z : ℂ, Polynomial.eval z p = f z) ∧
      ∀ k : ℕ, m < k → p.coeff k = 0 := by
  classical
  refine ⟨∑ n ∈ Finset.range (Nat.floor m + 1),
      Polynomial.C (((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)) * Polynomial.X ^ n, ?_, ?_⟩
  · intro z
    have key := Complex.taylorSeries_eq_of_entire' hf (c := (0 : ℂ)) (z := z)
    simp only [sub_zero] at key
    have hsum : ∑' n : ℕ, ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n)
        = ∑ n ∈ Finset.range (Nat.floor m + 1),
            ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n) := by
      refine tsum_eq_sum fun n hn => ?_
      have h0 : ¬ (n < Nat.floor m + 1) := by
        simpa [Finset.mem_range] using hn
      have h1 : Nat.floor m + 1 ≤ n := by omega
      have h2 : m < (n : ℝ) := (Nat.lt_floor_add_one m).trans_le (by exact_mod_cast h1)
      rw [hvanish n (by exact_mod_cast h2)]
      ring
    rw [← key, hsum, Polynomial.eval_finset_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · intro k hk
    rw [Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro n hn
    by_cases h : k = n
    · subst h
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, hvanish k hk]
      ring
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg h, mul_zero]
theorem apm_aunk04 :
    (apm_aunk04_polynomial.roots.filter (fun z => ‖z‖ < 1)).card = 0 ∧
      ∀ (f : ℂ → ℂ) (A B m : ℝ),
        0 < A → 0 < B → 0 < m →
        Differentiable ℂ f →
        (∀ z : ℂ, ‖f z‖ ≤ A + B * Real.rpow ‖z‖ m) →
        ∃ p : ℂ[X],
          (∀ z : ℂ, Polynomial.eval z p = f z) ∧
          ∀ k : ℕ, m < k → p.coeff k = 0 := by
  refine ⟨apm_aunk04_no_roots_in_unitDisk, ?_⟩
  intro f A B m hA hB hm hf hgrowth
  exact apm_aunk04_bridge_2 f m hf
    (apm_aunk04_bridge_1 f A B m hA hB hm hf hgrowth)
