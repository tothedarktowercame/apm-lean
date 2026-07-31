import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.MeanInequalitiesPow

open MeasureTheory Set ENNReal Filter Topology

noncomputable section

/-! # APM a02J02: Radon-Riesz theorem for Lp (1 < p < ∞)

  f_n → f a.e., ‖f_n‖_p → ‖f‖_p  ⟹  f_n → f in Lp.

  NOT in Mathlib as of 2026-03. Proof via Fatou's lemma on
  g_n = 2^{p-1}(|f_n|^p + |f|^p) - |f_n - f|^p ≥ 0.
-/

-- CLOSED: (s+t)^p ≤ 2^p (s^p + t^p) for s,t ≥ 0, nat p
lemma add_pow_le_two_pow_mul {p : ℕ} (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s + t) ^ p ≤ 2 ^ p * (s ^ p + t ^ p) := by
  have hst : s + t ≤ 2 * max s t := by
    calc s + t ≤ max s t + max s t := add_le_add (le_max_left s t) (le_max_right s t)
      _ = 2 * max s t := by ring
  have hmax : max s t ^ p ≤ s ^ p + t ^ p := by
    rcases le_total s t with h | h
    · simp [max_eq_right h]; linarith [pow_nonneg hs p]
    · simp [max_eq_left h]; linarith [pow_nonneg ht p]
  calc (s + t) ^ p
      ≤ (2 * max s t) ^ p := by gcongr
    _ = 2 ^ p * max s t ^ p := by rw [mul_pow]
    _ ≤ 2 ^ p * (s ^ p + t ^ p) := by gcongr

-- CLOSED: |a-b|^p ≤ 2^p (|a|^p + |b|^p) for nat p
lemma abs_sub_pow_le {p : ℕ} (a b : ℝ) :
    |a - b| ^ p ≤ 2 ^ p * (|a| ^ p + |b| ^ p) :=
  calc |a - b| ^ p
      ≤ (|a| + |b|) ^ p := by
        gcongr; exact norm_sub_le a b
    _ ≤ 2 ^ p * (|a| ^ p + |b| ^ p) :=
        add_pow_le_two_pow_mul |a| |b| (abs_nonneg a) (abs_nonneg b)

-- CLOSED: real-exponent version via the generalized mean inequality
lemma rpow_sub_le {p : ℝ} (hp : 1 ≤ p) (a b : ℝ) :
    |a - b| ^ p ≤ 2 ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  calc
    |a - b| ^ p ≤ (|a| + |b|) ^ p := by
      exact Real.rpow_le_rpow (abs_nonneg _) (abs_sub a b) (zero_le_one.trans hp)
    _ ≤ 2 ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
        ⟨|a|, abs_nonneg a⟩ ⟨|b|, abs_nonneg b⟩ hp

-- Radon-Riesz theorem statement
theorem radon_riesz {p : ℝ} (hp1 : 1 < p)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict (Icc 0 1)))
    (hae : ∀ᵐ x ∂(volume.restrict (Icc 0 1)),
      Tendsto (fun n => f n x) atTop (nhds (g x)))
    (hnorm : Tendsto
      (fun n => eLpNorm (f n) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)))
      atTop (nhds (eLpNorm g (ENNReal.ofReal p) (volume.restrict (Icc 0 1))))) :
    Tendsto
      (fun n => eLpNorm (f n - g) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)))
      atTop (nhds 0) := by
  -- Proof: Fatou on g_n = 2^{p-1}(|f_n|^p + |f|^p) - |f_n-f|^p ≥ 0
  -- g_n → 2^p|f|^p a.e., Fatou gives ∫ 2^p|f|^p ≤ lim inf ∫ g_n
  -- = 2^p‖f‖^p - lim sup ‖f_n-f‖^p, so lim sup ‖f_n-f‖^p ≤ 0.
  --
  -- Mathlib path:
  -- 1. rpow_sub_le for g_n ≥ 0
  -- 2. lintegral_liminf_le (Fatou for ennreal-valued integrals)
  -- 3. eLpNorm ↔ lintegral conversion via eLpNorm_rpow_eq_lintegral
  -- 4. Tendsto arithmetic for lim inf/lim sup
  --
  -- This theorem is genuinely absent from Mathlib (searched: Radon-Riesz,
  -- Brezis-Lieb, tendsto_Lp_of_tendsto_ae_of_tendsto_norm — none found).
  -- The closest: tendsto_Lp_of_tendsto_ae requires UnifIntegrable + UnifTight
  -- as hypotheses, which is a DIFFERENT theorem (Vitali convergence).
  --
  -- Precise remaining construction: first prove the Scheffé lemma for
  -- `u n x = |f n x| ^ p`.  The hypotheses give `u n → |g| ^ p` a.e. and,
  -- after rewriting with `eLpNorm_eq_lintegral_rpow_enorm_toReal`, convergence
  -- of their integrals.  Scheffé gives `u n → |g| ^ p` in L¹, hence uniform
  -- integrability of `u`.  The proved `rpow_sub_le` then transfers uniform
  -- integrability to `|f n - g| ^ p`; Vitali at exponent one and the same
  -- eLpNorm/lintegral rewrite finish the target.
  sorry
