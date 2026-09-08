import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory

namespace SardContinuousAddEquivQuasiMeasurePreservingProbe

variable {E F : Type*}
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [MeasurableSpace E] [BorelSpace E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F]
  [SecondCountableTopology F]

/-- A continuous additive equivalence is quasi-measure-preserving between
additive Haar measures when the target is locally compact and second countable. -/
theorem ContinuousAddEquiv.quasiMeasurePreserving_addHaar
    (e : E ≃ₜ+ F) (μ : Measure E) (ν : Measure F)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν] :
    Measure.QuasiMeasurePreserving (e : E → F) μ ν := by
  refine ⟨e.continuous.measurable, ?_⟩
  letI : Measure.IsAddHaarMeasure (μ.map e) := e.isAddHaarMeasure_map μ
  exact Measure.absolutelyContinuous_isAddHaarMeasure (μ.map e) ν

#print axioms ContinuousAddEquiv.quasiMeasurePreserving_addHaar

end SardContinuousAddEquivQuasiMeasurePreservingProbe
