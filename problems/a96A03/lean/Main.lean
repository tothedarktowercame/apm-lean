/-
! # APM a96A03: a.e. convergence in L² unit ball implies weak convergence

Let B = {f ∈ L²(ℝ) : ‖f‖₂ ≤ 1}. If {fₙ} ⊂ B and fₙ → f a.e., then:
(1) f ∈ B (by Fatou's lemma).
(2) ∫ fₙg → ∫ fg for all g ∈ L² (weak convergence, by density + DCT).
-/

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

/-- (1) The a.e. limit f belongs to the L² unit ball: ‖f‖₂ ≤ 1.

    Proof: Fatou's lemma (eLpNorm'_lim_le_liminf_eLpNorm') gives
    ‖f‖₂ ≤ lim inf ‖fₙ‖₂ ≤ 1. -/
theorem memLp_limit_of_ae_tendsto_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) volume)
    (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MemLp g 2 volume ∧ eLpNorm g 2 volume ≤ 1 := by
  -- Fatou's lemma for Lp norms: ‖g‖₂' ≤ lim inf ‖fₙ‖₂'
  have h_fatou : eLpNorm' g 2 volume ≤ atTop.liminf (fun n => eLpNorm' (f n) 2 volume) :=
    MeasureTheory.Lp.eLpNorm'_lim_le_liminf_eLpNorm' (by norm_num) hf_meas hae
  -- eLpNorm F 2 = eLpNorm' F 2 (for p = 2 ≠ 0, ≠ ∞)
  have h_eq (F : ℝ → ℝ) : eLpNorm F 2 volume = eLpNorm' F 2 volume :=
    eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  -- g is AEStronglyMeasurable (a.e. limit of AEStronglyMeasurable)
  have h_g_meas : AEStronglyMeasurable g volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hf_meas hae
  -- liminf of sequence bounded above by 1 is ≤ 1
  -- (Each eLpNorm (f n) 2 ≤ 1, so liminf ≤ 1)
  -- This is where the liminf API requires IsCoboundedUnder autoParam.
  -- We use the fact that the sequence is bounded above by 1.
  have h_g_norm_le : eLpNorm' g 2 volume ≤ 1 := by
    rw [show atTop.liminf (fun n => eLpNorm' (f n) 2 volume) =
            atTop.liminf (fun n => eLpNorm (f n) 2 volume) from by
        congr 1; ext n; exact (h_eq _).symm] at h_fatou
    have h_bdd : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => eLpNorm (f n) 2 volume) :=
      ⟨0, Eventually.of_forall (fun _ => by simp)⟩
    have h_liminf_le : atTop.liminf (fun n => eLpNorm (f n) 2 volume) ≤ 1 :=
      liminf_le_of_le h_bdd (fun b hb => by
        -- hb : ∀ᶠ n in atTop, b ≤ eLpNorm (f n) 2 volume
        -- Use: since atTop is NeBot, the eventually is non-trivial, so b ≤ 1
        rcases Filter.Eventually.exists hb with ⟨n, hn⟩
        exact hn.trans (hf_bdd n))
    exact h_fatou.trans h_liminf_le
  refine ⟨⟨h_g_meas, by rw [h_eq]; exact lt_of_le_of_lt h_g_norm_le (by norm_num)⟩,
          by rw [h_eq]; exact h_g_norm_le⟩

/-- (2) Weak convergence: ∫ fₙ h → ∫ f h for all h ∈ L²(ℝ).

    Proof: Approximate h ∈ L² by compactly supported continuous φ.
    For φ: use DCT on the compact support.
    For general h: Cauchy-Schwarz error bound ‖∫fₙ(h-φ)‖ ≤ ‖fₙ‖₂ · ‖h-φ‖₂ ≤ ‖h-φ‖₂. -/
theorem weak_convergence_of_ae_tendsto_L2_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {h : ℝ → ℝ} (hh : MemLp h 2 volume) :
    Tendsto (fun n => ∫ x, f n x * h x ∂volume)
      atTop (𝓝 (∫ x, g x * h x ∂volume)) := by
  sorry

end
