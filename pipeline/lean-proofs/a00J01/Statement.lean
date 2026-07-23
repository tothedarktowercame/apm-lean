import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter Set

noncomputable section

theorem a00J01
    (f : ℝ → ℝ)
    (hf : Memℒp f ⊤ (volume.restrict (Icc (0 : ℝ) 1))) :
    Tendsto (fun (p : ℝ≥0) => eLpNorm f (↑p) (volume.restrict (Icc (0 : ℝ) 1)))
      atTop (𝓝 (eLpNorm f ⊤ (volume.restrict (Icc (0 : ℝ) 1)))) := by
  sorry
