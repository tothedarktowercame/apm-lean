import ConstructionTargets.ChartCoordinateDimensionDropNullity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Fixed-chart coordinate nullity forces nonsurjectivity -/

open Set MeasureTheory
noncomputable section

namespace ConstructionTargets.FixedChartNullForcesNonsurjectivity

variable {X M E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- If the part of a map's range lying in one fixed extended-chart source has
null coordinate image, then the map is not surjective.  The contradiction is
entirely coordinate-local: surjectivity would make that image equal to the
nonempty open chart target, which has positive additive Haar measure. -/
theorem not_surjective_of_fixedChart_coordinateNull
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : X → M) (q : M)
    (hnull : μ (extChartAt I q ''
      (range f ∩ (extChartAt I q).source)) = 0) :
    ¬ Function.Surjective f := by
  intro hsurj
  have hrange : range f = univ := by
    exact Set.eq_univ_of_forall fun y ↦ hsurj y
  have hpiece : range f ∩ (extChartAt I q).source =
      (extChartAt I q).source := by
    rw [hrange, univ_inter]
  have hzero : μ (extChartAt I q).target = 0 := by
    rw [← (extChartAt I q).image_source_eq_target, ← hpiece]
    exact hnull
  have hopen : IsOpen (extChartAt I q).target :=
    isOpen_extChartAt_target q
  have hnonempty : (extChartAt I q).target.Nonempty :=
    ⟨extChartAt I q q, mem_extChartAt_target q⟩
  exact (hopen.measure_ne_zero μ hnonempty) hzero

#print axioms not_surjective_of_fixedChart_coordinateNull

end ConstructionTargets.FixedChartNullForcesNonsurjectivity
