import Mathlib

open Filter MeasureTheory Set

noncomputable section

/-!
# APM a00J02

## Statement repairs

None.

## Encoding notes

The function on `[0,1]` is represented by a function on `ℝ`, restricted to that
interval. Absolute continuity is encoded by Mathlib's
`AbsolutelyContinuousOnInterval`, and the square-integrability hypothesis uses
the ordinary derivative `deriv f`.
-/

/-- FTC: for absolutely continuous f with f(0) = 0,
    f x = ∫ t in 0..x, deriv f t for x ∈ [0,1].
    Uses `AbsolutelyContinuousOnInterval.mono` to restrict to subinterval [0,x],
    then `integral_deriv_eq_sub`. -/
lemma ftc_a00j02 (f : ℝ → ℝ)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hf_zero : f 0 = 0)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    f x = ∫ t in (0)..x, deriv f t := by
  have hsub : uIcc 0 x ⊆ uIcc 0 1 := by
    intro y hy
    rw [mem_uIcc] at hy ⊢
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, le_trans h2 hx1⟩
    · left
      have hy0 : y = 0 := by linarith
      constructor <;> linarith
  have hac := hf_ac.mono hsub
  have h := hac.integral_deriv_eq_sub
  rw [hf_zero] at h
  linarith

/-- Absolute continuity of the Lebesgue integral:
    ∫ t in Icc 0 x, g t → 0 as x → 0⁺ when g ≥ 0 is integrable on Icc 0 1.
    BLOCKER: needs `tendsto_integral_filter_of_dominated_convergence` (DCT)
    applied to the family F(x)(t) = g(t) · indicator(Icc 0 x)(t) on the
    restricted measure μ = volume.restrict(Icc 0 1).
    - API searched: `tendsto_integral_filter_of_dominated_convergence`,
      `tendsto_setIntegral_of_L1`, `tendsto_integral_of_L1`
    - `nhdsWithin 0 (Ioi 0)` is countably generated (confirmed).
    - F(x) → 0 a.e. on Icc 0 1 for x → 0⁺ (clear: for t > 0, t ∉ Icc 0 x eventually).
    - |F(x)| ≤ g ∈ L¹(μ).
    - Remaining work: assemble AEStronglyMeasurable, pointwise limit, domination. -/
lemma tendsto_setIntegral_Icc_zero
    (g : ℝ → ℝ)
    (hg_nn : 0 ≤ g)
    (hg : IntegrableOn g (Icc (0 : ℝ) 1) volume) :
    Tendsto (fun x => ∫ t in Icc (0 : ℝ) x, g t ∂volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  sorry

/-- Cauchy-Schwarz bound: for x ∈ (0,1],
    |∫ t in Icc 0 x, deriv f t| ≤ √x · (∫ t in Icc 0 x, |deriv f t|²)^{1/2}.
    BLOCKER: needs Hölder inequality with p = q = 2 for set integrals.
    - API searched: `integral_mul_le_Lp_mul_Lq_of_nonneg`, `integral_mul_norm_le_Lp_mul_Lq`,
      `Real.two_two` (HolderConjugate 2 2)
    - These require `MemLp` hypotheses with `ENNReal.ofReal 2`.
    - Also needs `abs_integral_le_integral_abs` as a first step.
    - Could also prove from scratch: expand (∫ (|g| - c·1)² ≥ 0 and optimize c. -/
lemma cauchy_schwarz_bound (f : ℝ → ℝ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hf_deriv_sq :
      IntegrableOn (fun x ↦ |deriv f x| ^ 2) (Icc (0 : ℝ) 1) volume) :
    |∫ t in Icc (0 : ℝ) x, deriv f t ∂volume| ≤
      Real.sqrt x * Real.sqrt (∫ t in Icc (0 : ℝ) x, |deriv f t| ^ 2 ∂volume) := by
  sorry

theorem apm_a00j02
    (f : ℝ → ℝ)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hf_zero : f 0 = 0)
    (hf_deriv_sq :
      IntegrableOn (fun x ↦ |deriv f x| ^ 2) (Icc (0 : ℝ) 1) volume) :
    Tendsto (fun x ↦ f x / Real.sqrt x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  -- Proof sketch:
  -- 1. FTC (proved as `ftc_a00j02`): f x = ∫₀ˣ deriv f for x ∈ [0,1]
  -- 2. Cauchy-Schwarz (BLOCKER: `cauchy_schwarz_bound`):
  --    |f x / √x| ≤ (∫₀ˣ |deriv f|²)^{1/2}
  -- 3. Abs. continuity of integral (BLOCKER: `tendsto_setIntegral_Icc_zero`):
  --    ∫₀ˣ |deriv f|² → 0 as x → 0⁺
  -- 4. Squeeze: f x / √x → 0
  --
  -- PARTIAL: FTC proved (`ftc_a00j02`), two helper lemmas blocked.
  -- `tendsto_setIntegral_Icc_zero`: needs DCT for dominated convergence of integrals
  -- `cauchy_schwarz_bound`: needs Hölder/Cauchy-Schwarz for set integrals
  -- Main theorem needs both + squeeze argument. All three sorries documented above.
  sorry

end
