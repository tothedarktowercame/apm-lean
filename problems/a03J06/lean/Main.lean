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
  /-
  CLOSER HOP 2 (partial): `apm_a03J06_iteratedDeriv_eq_zero_of_natDegree_lt`
  now sends the hop-1 Cauchy bound to zero along radii `R = 2^n`, proving

      m < k → iteratedDeriv k f 0 = 0.

  This closes the asymptotic half without adding a sign assumption on `A`.
  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's
  analytic uniqueness and complex-polynomial sources, sibling artifacts, and
  git history found no compiled theorem reconstructing a global entire
  function from finitely supported iterated derivatives at one point.  The
  remaining step is to form the Taylor polynomial through degree `m`, prove
  local equality from the coefficient formula, and propagate it globally by
  analytic uniqueness. The frozen statement is unchanged; no defect was found.
  -/
  sorry
