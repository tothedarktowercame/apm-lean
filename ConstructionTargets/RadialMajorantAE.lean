import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set Filter Real Topology

open scoped ENNReal

noncomputable section

namespace ConstructionTargets.RadialMajorantAE

/-- Tonelli's theorem in the radial layer-cake form.  No integrability
hypothesis is required because both sides are nonnegative extended integrals.

The endpoint convention (`Ici`/`Icc`) is convenient for exact rewriting; for
Lebesgue measure it is equivalent to the usual strict inequalities. -/
theorem lintegral_mul_radial_layerCake
    {g w φ : ℝ → ℝ≥0∞} (hg : Measurable g) (hw : Measurable w)
    (hφ : ∀ t, φ t = ∫⁻ s in Ici |t|, w s ∂volume) :
    ∫⁻ t, g t * φ t ∂volume =
      ∫⁻ s, w s * (∫⁻ t in Icc (-s) s, g t ∂volume) ∂volume := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun t s =>
    if |t| ≤ s then g t * w s else 0
  have hF : Measurable (Function.uncurry F) := by
    apply Measurable.ite
    · exact measurableSet_le measurable_fst.norm measurable_snd
    · exact (hg.comp measurable_fst).mul (hw.comp measurable_snd)
    · exact measurable_const
  calc
    (∫⁻ t, g t * φ t ∂volume) =
        ∫⁻ t, g t * (∫⁻ s in Ici |t|, w s ∂volume) ∂volume := by
      apply lintegral_congr
      intro t
      rw [hφ t]
    _ = ∫⁻ t, ∫⁻ s, F t s ∂volume ∂volume := by
      apply lintegral_congr
      intro t
      rw [← lintegral_const_mul _ hw]
      rw [← lintegral_indicator measurableSet_Ici]
      apply lintegral_congr
      intro s
      simp only [Set.indicator, mem_Ici, F]
    _ = ∫⁻ s, ∫⁻ t, F t s ∂volume ∂volume :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ s, w s * (∫⁻ t in Icc (-s) s, g t ∂volume) ∂volume := by
      apply lintegral_congr
      intro s
      calc
        (∫⁻ t, F t s ∂volume) =
            ∫⁻ t in Icc (-s) s, g t * w s ∂volume := by
          rw [← lintegral_indicator measurableSet_Icc]
          apply lintegral_congr
          intro t
          simp only [Set.indicator, mem_Icc, F]
          by_cases h : |t| ≤ s
          · have hs : -s ≤ t ∧ t ≤ s := by simpa [abs_le, and_comm] using h
            simp [h, hs]
          · have hs : ¬(-s ≤ t ∧ t ≤ s) := by
              simpa [abs_le, and_comm] using h
            simp [h, hs]
        _ = (∫⁻ t in Icc (-s) s, g t ∂volume) * w s := by
          exact lintegral_mul_const (w s) hg
        _ = w s * (∫⁻ t in Icc (-s) s, g t ∂volume) := mul_comm _ _

end ConstructionTargets.RadialMajorantAE
