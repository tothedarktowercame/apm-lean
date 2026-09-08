import ConstructionTargets.SardCompactProjectedChartNullityOfResidualData

open MeasureTheory

namespace SardFiniteDimensionalBorelAddHaarPackageProbe

/-- Every finite-dimensional real normed space admits its Borel measurable
structure together with a canonical additive Haar measure. -/
theorem exists_borel_addHaarMeasure
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    letI : MeasurableSpace V := borel V
    letI : BorelSpace V := ⟨rfl⟩
    ∃ μ : Measure V, Measure.IsAddHaarMeasure μ := by
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  exact ⟨Measure.addHaar, inferInstance⟩

#print axioms exists_borel_addHaarMeasure

end SardFiniteDimensionalBorelAddHaarPackageProbe
