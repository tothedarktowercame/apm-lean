import Mathlib

/-!
# Strong continuity of translations in `L²(ℝ)`

This module packages the reusable translation-continuity input used by
approximate-identity and convolution arguments.
-/

open MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

namespace ConstructionTargets.L2Translation

/-- Translations are strongly continuous in `L²(ℝ)`: if `f ∈ L²`, then
`‖f(· - t) - f‖₂ → 0` as `t → 0`. -/
theorem eLpNorm_translation_tendsto
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    Tendsto (fun t => eLpNorm (fun x => f (x - t) - f x) 2 volume)
      (𝓝 0) (𝓝 0) := by
  let g : ℝ → C(ℝ, ℝ) := fun t =>
    ⟨fun x => x - t, continuous_id.sub continuous_const⟩
  have hg : Continuous g := by
    let G : C(ℝ × ℝ, ℝ) :=
      ⟨fun p => p.2 - p.1, continuous_snd.sub continuous_fst⟩
    exact (ContinuousMap.curry G).continuous
  have hgm : ∀ t, MeasurePreserving (g t) volume volume := by
    intro t
    simpa [g, sub_eq_add_neg] using measurePreserving_add_right volume (-t)
  let F : ℝ → Lp ℝ 2 volume := fun t =>
    Lp.compMeasurePreserving (g t) (hgm t) (hf.toLp f)
  have hF : Continuous F := by
    dsimp [F]
    exact continuous_const.compMeasurePreservingLp hg hgm (by simp)
  have hF0 : F 0 = hf.toLp f := by
    dsimp [F]
    rw [Lp.toLp_compMeasurePreserving]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by simp [g]
  have hed : Tendsto (fun t => edist (F t) (hf.toLp f)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun _ : ℝ => hf.toLp f) := continuous_const
    simpa [hF0] using (hF.edist hc).tendsto 0
  convert hed using 1
  ext t
  dsimp [F]
  rw [Lp.toLp_compMeasurePreserving]
  rw [Lp.edist_toLp_toLp]
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [g]

end ConstructionTargets.L2Translation
