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
  obtain ⟨C, hC⟩ := hbdd
  have hp_top : p ≠ ∞ := ne_of_lt (hp2.trans_le le_top)
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (by positivity) hp_top
  have hp2_real : p.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal hp_top (by norm_num)).2 hp2
  let r : ℝ := 1 / p.toReal - 1 / 2
  have hr : 0 < r := by
    dsimp [r]
    exact sub_pos.2 (one_div_lt_one_div_of_lt hp_pos hp2_real)
  intro ε hε
  let D : ℝ := C + 1
  have hD : 0 < D := by
    dsimp [D]
    positivity
  let δ : ℝ := (ε / D) ^ (1 / r)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact Real.rpow_pos_of_pos (div_pos hε hD) _
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  calc
    eLpNorm (f n) p (μ.restrict s) ≤
        eLpNorm (f n) 2 (μ.restrict s) *
          (μ.restrict s) univ ^ r := by
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2.le
        ((hfm n).mono_measure Measure.restrict_le_self)
    _ ≤ eLpNorm (f n) 2 μ * μ s ^ r := by
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul'
        (eLpNorm_mono_measure (f n) Measure.restrict_le_self)
        (ENNReal.rpow_le_rpow le_rfl hr.le)
    _ ≤ (C : ℝ≥0∞) * μ s ^ r :=
      mul_le_mul_left (hC n) _
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal δ ^ r := by
      exact mul_le_mul_right (ENNReal.rpow_le_rpow hμs hr.le) _
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal δ ^ r := by
      gcongr
      rw [ENNReal.coe_nnreal_eq]
      exact ENNReal.ofReal_le_ofReal (by dsimp [D]; linarith)
    _ = ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_rpow_of_pos hδ, ← ENNReal.ofReal_mul hD.le]
      congr 1
      dsimp [δ]
      rw [← Real.rpow_mul (le_of_lt (div_pos hε hD)),
        one_div_mul_cancel hr.ne', Real.rpow_one,
        mul_div_cancel₀ ε hD.ne']

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
  obtain ⟨C, hC⟩ := hbdd
  have hg2_norm : eLpNorm g 2 μ ≤ C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hC) hfm hae
  have hg2 : MemLp g 2 μ :=
    ⟨hgm, hg2_norm.trans_lt ENNReal.coe_lt_top⟩
  have hgp : MemLp g p μ := hg2.mono_exponent hp2.le
  have hui : UnifIntegrable f p μ :=
    unifIntegrable_of_L2_bounded hfm hf2 ⟨C, hC⟩ hp1 hp2
  simpa only [Pi.sub_apply] using
    tendsto_Lp_finite_of_tendsto_ae hp1 (ne_of_lt (hp2.trans_le le_top))
      hfm hgp hui hae

end ApmCanaries.A93A02
