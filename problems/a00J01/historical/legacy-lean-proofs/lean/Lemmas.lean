import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Analysis.NormedSpace.Basic

open MeasureTheory ENNReal

noncomputable section

/-- Upper bound: eLpNorm f p μ ≤ eLpNorm f ⊤ μ for finite measure spaces. -/
lemma eLpNorm_le_eLpNorm_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    eLpNorm f p μ ≤ eLpNorm f ⊤ μ * (μ Set.univ) ^ (1 / p) := by
  sorry

/-- Lower bound: for any α < essSup |f|, the Lp norm is at least α · μ(E_α)^{1/p}. -/
lemma eLpNorm_ge_of_essSup
    {α' : Type*} [MeasurableSpace α'] {μ : Measure α'} [IsFiniteMeasure μ]
    {f : α' → ℝ} (hf : AEStronglyMeasurable f μ)
    {c : ℝ≥0∞} (hc : c < eLpNorm f ⊤ μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    c * (μ {x | c < ‖f x‖₊}).toNNReal ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
  sorry
