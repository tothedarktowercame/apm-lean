import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

open MeasureTheory Filter

noncomputable section

/-- For f ∈ L^∞([0,1]), the Lp norms converge to the essential supremum as p → ∞. -/
theorem lp_norm_tendsto_essSup
    (f : α → ℝ) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (hf : Memℒp f ⊤ μ) :
    Tendsto (fun (p : ℝ) => eLpNorm f (ENNReal.ofReal p) μ) atTop
      (nhds (eLpNorm f ⊤ μ)) := by
  sorry
