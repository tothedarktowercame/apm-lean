import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# APM a93A02: L²-bounded a.e. convergence implies Lp convergence for p < 2

**Problem.** Let {fₙ} ⊂ L²([0,1]) with sup ‖fₙ‖₂ < ∞. If fₙ → f a.e. and
1 ≤ p < 2, then ‖fₙ - f‖ₚ → 0.

## Proof strategy

By Vitali's convergence theorem (`tendsto_Lp_finite_of_tendsto_ae`):
a.e. convergence + uniform integrability ⟹ Lp convergence.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter ENNReal
open scoped Topology

namespace ApmCanaries.A93A02

/-- Uniform integrability of {fₙ} in Lp from L² bound.

    **SORRY BOUNDARY:** If each fₙ ∈ L² with uniform bound M, and p < 2,
    then {fₙ} is uniformly integrable in Lp. The Hölder inequality gives
    ‖fₙ · 1_S‖ₚ ≤ ‖fₙ‖₂ · μ(S)^{1/p - 1/2}, which is uniform in n.
    Connecting this to the `UnifIntegrable` definition requires
    `MemLp.eLpNorm_indicator_le` applied with the uniform L² bound. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): use a finite NNReal L² bound,
-- since an ENNReal witness could be `⊤` and make boundedness vacuous.
lemma unifIntegrable_of_L2_bounded
    {f : ℕ → ℝ → ℝ} {μ : Measure ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hf2 : ∀ n, MemLp (f n) 2 μ)
    (hbdd : ∃ C : NNReal, ∀ n, eLpNorm (f n) 2 μ ≤ C)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2) :
    UnifIntegrable f p μ := by
  sorry

/-- **Main theorem:** L²-bounded a.e. convergence implies Lp convergence
    for 1 ≤ p < 2 on [0,1]. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): use a finite NNReal L² bound,
-- since an ENNReal witness could be `⊤` and make boundedness vacuous.
theorem tendsto_Lp_of_ae_tendsto_of_L2_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {μ : Measure ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hgm : AEStronglyMeasurable g μ)
    (hf2 : ∀ n, MemLp (f n) 2 μ)
    (hbdd : ∃ C : NNReal, ∀ n, eLpNorm (f n) 2 μ ≤ C)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    [IsFiniteMeasure μ] :
    Tendsto (fun n => eLpNorm (fun x => f n x - g x) p μ) atTop (𝓝 0) := by
  -- g ∈ Lp (Fatou + finite measure embedding L² → Lp)
  have hg2 : MemLp g 2 μ := by sorry
  have hgp : MemLp g p μ := by sorry
  -- fₙ uniformly integrable in Lp
  have hui : UnifIntegrable f p μ :=
    unifIntegrable_of_L2_bounded hfm hf2 hbdd hp1 hp2
  -- {fₙ - g} is also UI
  have hui_sub : UnifIntegrable (fun n x => f n x - g x) p μ := by sorry
  -- hₙ = fₙ - g → 0 a.e.
  set h : ℕ → ℝ → ℝ := fun n x => f n x - g x with hh_def
  have hhn : ∀ n, AEStronglyMeasurable (h n) μ :=
    fun n => by rw [hh_def]; exact AEStronglyMeasurable.sub (hfm n) hgm
  have hh0 : MemLp (fun _ => (0 : ℝ)) p μ := MemLp.zero
  have hhae : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 0) := by
    filter_upwards [hae] with x hx
    rw [hh_def]
    have : Tendsto (fun n => f n x - g x) atTop (𝓝 (g x - g x)) :=
      Tendsto.sub hx tendsto_const_nhds
    simp at this
    exact this
  have hp_ne_top : p ≠ ∞ := (lt_of_lt_of_le hp2 (by norm_num : (2:ℝ≥0∞) ≤ ∞)).ne
  have hhui : UnifIntegrable h p μ := by
    rw [hh_def]
    exact hui_sub
  have hresult := tendsto_Lp_finite_of_tendsto_ae hp1 hp_ne_top hhn hh0 hhui hhae
  convert hresult using 1
  funext n
  rw [show (fun x => f n x - g x) = h n from by rw [hh_def]]
  exact eLpNorm_congr_ae (ae_of_all _ fun _ => by simp)

end ApmCanaries.A93A02
