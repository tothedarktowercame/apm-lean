/-
! # APM a93J02: Σ (-1)ⁿ/(n+1) = log 2

Apply the dominated convergence theorem (via Abel's limit theorem) to
justify that Σ_{n=0}^∞ (-1)ⁿ/(n+1) = log 2.

Note: Since the alternating harmonic series is conditionally convergent,
Mathlib's `HasSum` (which requires unconditional/absolute convergence) does
not apply. We prove the result as the limit of partial sums.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Set Filter Topology Real

noncomputable section

/-- ∫₀¹ 1/(1+x) dx = log 2. -/
lemma integral_inv_one_plus_x : ∫ x in (0:ℝ)..1, 1 / (1 + x) = log 2 := by
  have h : ∫ x in (1:ℝ)..2, x⁻¹ = log 2 := by
    rw [integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  have key : ∫ x in (0:ℝ)..1, (x + 1)⁻¹ = ∫ x in (1:ℝ)..2, x⁻¹ := by
    have := intervalIntegral.integral_comp_add_right (f := fun y => y⁻¹) (a := 0) (b := 1) 1
    convert this using 1
    all_goals norm_num
  rw [show (∫ x in (0:ℝ)..1, 1 / (1 + x)) =
        ∫ x in (0:ℝ)..1, ((x + 1)⁻¹ : ℝ) from by
        congr with x; rw [one_div, add_comm 1 x]]
  rw [key, h]

/-- The power series associated to the alternating harmonic series is
    `log (1 + x) / x` inside its radius of convergence. -/
private lemma tsum_alternating_harmonic_mul_pow {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∑' n : ℕ, ((-1 : ℝ) ^ n / (↑n + 1)) * x ^ n = log (1 + x) / x := by
  have hneg : |(-x : ℝ)| < 1 := by simpa [abs_of_pos hx₀] using hx₁
  have hs := (hasSum_pow_div_log_of_abs_lt_one hneg).mul_left (-1 / x)
  have hs' : HasSum (fun n : ℕ => ((-1 : ℝ) ^ n / (↑n + 1)) * x ^ n)
      (log (1 + x) / x) := by
    have hterms : HasSum (fun n : ℕ => ((-1 : ℝ) ^ n / (↑n + 1)) * x ^ n)
        (-1 / x * -log (1 - -x)) :=
      hs.congr_fun (fun n => by
        rw [neg_pow]
        field_simp [hx₀.ne']
        rw [pow_succ, neg_pow]
        ring)
    convert hterms using 1
    field_simp [hx₀.ne']
    ring
  exact hs'.tsum_eq

/-- The alternating harmonic series converges.

    Uses the alternating series test: 1/(n+1) is antitone and tends to 0. -/
theorem tendsto_sum_alternating_harmonic :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 (log 2)) := by
  -- Step 1: Alternating series test gives convergence
  -- f(i) = 1/(i+1) is antitone and → 0
  have hf_antitone : Antitone fun (i : ℕ) => (1 : ℝ) / (↑i + 1) := by
    intro i j hij
    have hle : (↑i + 1 : ℝ) ≤ (↑j + 1) := by
      have : (↑i : ℝ) ≤ (↑j : ℝ) := mod_cast hij
      linarith
    exact one_div_le_one_div (by linarith : (0 : ℝ) < ↑j + 1) (by linarith : (0 : ℝ) < ↑i + 1)
      |>.mpr hle
  have hf_zero : Tendsto (fun i : ℕ => (1 : ℝ) / (↑i + 1)) atTop (𝓝 0) := by
    have h_cast : Tendsto (fun i : ℕ => (↑i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h_shift : Tendsto (fun i : ℕ => (↑(i + 1) : ℝ)) atTop atTop := by
      exact tendsto_atTop_mono
        (fun i => (show (↑i : ℝ) ≤ ↑(i + 1) from Nat.cast_le.mpr (Nat.le_succ i))) h_cast
    exact (tendsto_inv_atTop_zero.comp h_shift).congr
      fun i => by simp [one_div, Nat.cast_add_one]
  obtain ⟨l, hl⟩ :=
    Antitone.tendsto_alternating_series_of_tendsto_zero hf_antitone hf_zero
  -- Convert to the right form
  have hl' : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 l) := by
    have : ∀ n, ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((1 : ℝ) / (↑i + 1)) =
        ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1) := by
      intro n; congr with i; rw [mul_one_div]
    exact hl.congr this
  -- Step 2: Abel's limit theorem
  have abel := tendsto_tsum_powerSeries_nhdsWithin_lt hl'
  -- Step 3: identify the power series with `log (1 + x) / x` and let `x → 1⁻`.
  let F := fun x : ℝ =>
    ∑' n : ℕ, ((-1 : ℝ) ^ n / (↑n + 1)) * x ^ n
  have hmul : Tendsto (fun x => x * F x) (𝓝[<] (1 : ℝ)) (𝓝 l) := by
    have hid : Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id
    simpa only [F, one_mul] using hid.mul abel
  have hmul_eq_log : ∀ᶠ x in 𝓝[<] (1 : ℝ), x * F x = log (1 + x) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    dsimp only [F]
    rw [tsum_alternating_harmonic_mul_pow hx.1 hx.2]
    field_simp [hx.1.ne']
  have hlog_l : Tendsto (fun x : ℝ => log (1 + x)) (𝓝[<] (1 : ℝ)) (𝓝 l) :=
    hmul.congr' hmul_eq_log
  have hlog_two :
      Tendsto (fun x : ℝ => log (1 + x)) (𝓝[<] (1 : ℝ)) (𝓝 (log 2)) := by
    have hcont : ContinuousAt (fun x : ℝ => log (1 + x)) 1 :=
      (continuousAt_const.add continuousAt_id).log (by norm_num)
    have ht := tendsto_nhdsWithin_of_tendsto_nhds (s := Iio (1 : ℝ)) hcont.tendsto
    convert ht using 1
    all_goals norm_num
  have hl_eq : l = log 2 := tendsto_nhds_unique hlog_l hlog_two
  rwa [hl_eq] at hl'

/-- Main theorem: Σ (-1)ⁿ/(n+1) = log 2 (as limit of partial sums). -/
theorem alternating_harmonic_eq_log_two :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 (log 2)) :=
  tendsto_sum_alternating_harmonic

end
