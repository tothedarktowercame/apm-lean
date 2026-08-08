import Mathlib

/-!
# APM a03J06 — entire functions of polynomial growth

## Statement repairs

None. The statement is slightly strengthened by allowing `m = 0`; the same
conclusion then says that `f` is constant.

## Encoding questions

None. The conclusion uses an actual complex polynomial and identifies the
given entire function with its evaluation function pointwise.
-/

noncomputable section

/-- Cauchy's estimate with the theorem's polynomial-growth bound substituted
on a sphere of arbitrary radius greater than one.  This is adapted from the
compiled arbitrary-radius estimate in sibling `aunk04`. -/
lemma apm_a03J06_growth_cauchy_bound
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (A : ℝ) (m k : ℕ)
    (hbound : ∀ z : ℂ, 1 < ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m)
    {R : ℝ} (hR : 1 < R) :
    ‖iteratedDeriv k f 0‖ ≤ k.factorial * (A * R ^ m) / R ^ k := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (lt_trans zero_lt_one hR) hf.diffContOnCl
  intro z hz
  have hnorm : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  simpa [hnorm] using hbound z (hnorm.symm ▸ hR)

lemma apm_a03J06_iteratedDeriv_eq_zero_of_natDegree_lt
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (A : ℝ) (m k : ℕ)
    (hbound : ∀ z : ℂ, 1 < ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m)
    (hmk : m < k) :
    iteratedDeriv k f 0 = 0 := by
  rw [← norm_eq_zero]
  apply le_antisymm _ (norm_nonneg _)
  have hp : 0 < k - m := Nat.sub_pos_of_lt hmk
  have ht : Filter.Tendsto (fun n : ℕ ↦ (k.factorial : ℝ) * A /
      (2 : ℝ) ^ (n * (k - m)))
      Filter.atTop (nhds 0) := by
    have hb := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 2⁻¹ by positivity) (show (2 : ℝ)⁻¹ < 1 by norm_num)
    have hpw := hb.pow (k - m)
    have hc : Filter.Tendsto (fun _ : ℕ ↦ (k.factorial : ℝ) * A)
        Filter.atTop (nhds ((k.factorial : ℝ) * A)) := tendsto_const_nhds
    have hmul := hc.mul hpw
    simpa [pow_mul, hp.ne'] using hmul
  apply ge_of_tendsto ht
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
  have hR : (1 : ℝ) < 2 ^ n := one_lt_pow₀ (by norm_num) (Nat.ne_zero_of_lt hn)
  have h := apm_a03J06_growth_cauchy_bound f hf A m k hbound hR
  have hRm : ((2 : ℝ) ^ n) ^ m ≠ 0 := pow_ne_zero _ (by positivity)
  have hpow : ((2 : ℝ) ^ n) ^ k =
        ((2 : ℝ) ^ n) ^ m * ((2 : ℝ) ^ n) ^ (k - m) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hmk)]
  rw [hpow] at h
  calc
    ‖iteratedDeriv k f 0‖ ≤
        k.factorial * (A * ((2 : ℝ) ^ n) ^ m) /
          (((2 : ℝ) ^ n) ^ m * ((2 : ℝ) ^ n) ^ (k - m)) := h
    _ = (k.factorial : ℝ) * A / (2 : ℝ) ^ (n * (k - m)) := by
      rw [pow_mul]
      field_simp

theorem apm_a03j06 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (A : ℝ) (m : ℕ)
    (hbound : ∀ z : ℂ, 1 < ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z : ℂ, f z = p.eval z := by
  let c : ℕ → ℂ := fun k => iteratedDeriv k f 0 / k.factorial
  let p : Polynomial ℂ :=
    ∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (c k)
  have hc : ∀ k, m + 1 ≤ k → c k = 0 := by
    intro k hk
    exact div_eq_zero_iff.mpr (Or.inl
      (apm_a03J06_iteratedDeriv_eq_zero_of_natDegree_lt
        f hf A m k hbound (by omega)))
  have hpdeg : p.natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp [p, Polynomial.coeff_monomial]
    omega
  refine ⟨p, hpdeg, ?_⟩
  have hfAnalytic : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hseries := (hfAnalytic 0 (Set.mem_univ 0)).hasFPowerSeriesAt
  have hevent : f =ᶠ[nhds 0] fun z => p.eval z := by
    filter_upwards [hseries.eventually_hasSum] with z hsum
    have hzero : ∀ k ∉ Finset.range (m + 1), c k * z ^ k = 0 := by
      intro k hk
      have hk' : m + 1 ≤ k := by simpa using hk
      simpa only [hc k hk', zero_mul]
    have hsummable : Summable (fun k : ℕ => c k * z ^ k) :=
      summable_of_ne_finset_zero hzero
    have hfinite : HasSum (fun k : ℕ => c k * z ^ k)
        (∑ k ∈ Finset.range (m + 1), c k * z ^ k) := by
      have heq := tsum_eq_sum (L := SummationFilter.unconditional ℕ) hzero
      rw [← heq]
      exact hsummable.hasSum
    have hsum' : HasSum (fun k : ℕ => c k * z ^ k) (f z) := by
      simpa [c, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hsum
    have heq := hsum'.unique hfinite
    simpa [p, Polynomial.eval_finset_sum] using heq
  have hpeq : f = fun z => p.eval z :=
    hfAnalytic.eq_of_eventuallyEq (AnalyticOnNhd.eval_polynomial p) hevent
  intro z
  exact congrFun hpeq z
