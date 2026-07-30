/-
! # APM a96A03: a.e. convergence in L² unit ball implies weak convergence

Let B = {f ∈ L²(ℝ) : ‖f‖₂ ≤ 1}. If {fₙ} ⊂ B and fₙ → f a.e., then:
(1) f ∈ B (by Fatou's lemma).
(2) ∫ fₙg → ∫ fg for all g ∈ L² (weak convergence, by density + DCT).
-/

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.UnifTight
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

    Proof: Hölder's inequality and the fixed L² test function show that the products
    `fₙh` are uniformly integrable and uniformly tight in L¹.  Their a.e. convergence
    to `gh` therefore upgrades to L¹ convergence by Vitali's theorem. -/
theorem weak_convergence_of_ae_tendsto_L2_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {h : ℝ → ℝ} (hh : MemLp h 2 volume) :
    Tendsto (fun n => ∫ x, f n x * h x ∂volume)
      atTop (𝓝 (∫ x, g x * h x ∂volume)) := by
  let F : ℕ → ℝ → ℝ := fun n x => f n x * h x
  let G : ℝ → ℝ := fun x => g x * h x
  have hfLp (n : ℕ) : MemLp (f n) 2 volume :=
    ⟨hf_meas n, (hf_bdd n).trans_lt (by norm_num)⟩
  have hg_norm : eLpNorm g 2 volume ≤ 1 :=
    (memLp_limit_of_ae_tendsto_bounded hf_meas hf_bdd hae).2
  have hgLp : MemLp g 2 volume :=
    ⟨hg_meas, hg_norm.trans_lt (by norm_num)⟩
  have hFLp (n : ℕ) : MemLp (F n) 1 volume := by
    simpa [F, mul_comm] using (hh.mul' (hfLp n) : MemLp (fun x => f n x * h x) 1 volume)
  have hGLp : MemLp G 1 volume := by
    simpa [G, mul_comm] using (hh.mul' hgLp : MemLp (fun x => g x * h x) 1 volume)
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) volume := (hFLp n).1
  have hUI : UnifIntegrable F 1 volume := by
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := hh.eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    have hind :
        s.indicator (F n) = fun x => f n x * s.indicator h x := by
      ext x
      by_cases hx : x ∈ s <;> simp [F, hx]
    rw [hind]
    calc
      eLpNorm (fun x => f n x * s.indicator h x) 1 volume
          ≤ eLpNorm (f n) 2 volume * eLpNorm (s.indicator h) 2 volume := by
            simpa [Pi.smul_apply, smul_eq_mul] using
              (eLpNorm_smul_le_mul_eLpNorm
                ((hh.1.indicator hs)) (hf_meas n) :
                eLpNorm ((f n) • s.indicator h) 1 volume ≤
                  eLpNorm (f n) 2 volume * eLpNorm (s.indicator h) 2 volume)
      _ ≤ 1 * ENNReal.ofReal ε := mul_le_mul (hf_bdd n) (hsmall s hs hμs) (by simp) (by simp)
      _ = ENNReal.ofReal ε := one_mul _
  have hUT : UnifTight F 1 volume := by
    intro ε hε
    obtain ⟨s, hs, hμs, htail⟩ :=
      hh.exists_eLpNorm_indicator_compl_lt (by norm_num) (ENNReal.coe_ne_zero.mpr hε.ne')
    refine ⟨s, ne_of_lt hμs, fun n => ?_⟩
    have hind :
        sᶜ.indicator (F n) = fun x => f n x * sᶜ.indicator h x := by
      ext x
      by_cases hx : x ∈ sᶜ <;> simp [F, hx]
    rw [hind]
    calc
      eLpNorm (fun x => f n x * sᶜ.indicator h x) 1 volume
          ≤ eLpNorm (f n) 2 volume * eLpNorm (sᶜ.indicator h) 2 volume := by
            simpa [Pi.smul_apply, smul_eq_mul] using
              (eLpNorm_smul_le_mul_eLpNorm
                (hh.1.indicator hs.compl) (hf_meas n) :
                eLpNorm ((f n) • sᶜ.indicator h) 1 volume ≤
                  eLpNorm (f n) 2 volume * eLpNorm (sᶜ.indicator h) 2 volume)
      _ ≤ 1 * (ε : ℝ≥0∞) :=
        mul_le_mul (hf_bdd n) htail.le (by simp) (by simp)
      _ = (ε : ℝ≥0∞) := one_mul _
  have hFGae : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
    filter_upwards [hae] with x hx
    exact hx.mul_const (h x)
  have hL1 :
      Tendsto (fun n => eLpNorm (F n - G) 1 volume) atTop (𝓝 0) :=
    tendsto_Lp_of_tendsto_ae (by norm_num) (by norm_num) hFmeas hGLp hUI hUT hFGae
  simpa [F, G] using
    tendsto_integral_of_L1' G (memLp_one_iff_integrable.mp hGLp)
      (Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hFLp n)) hL1

end
