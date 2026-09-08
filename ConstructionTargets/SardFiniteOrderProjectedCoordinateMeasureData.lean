import ConstructionTargets.SardDerivativeRangeOrthogonalMeasurePackage

open MeasureTheory
namespace SardFiniteOrderProjectedCoordinateMeasureDataProbe

theorem exists_projected_coordinate_measure_data
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L) :
    let R := LinearMap.range L.toLinearMap
    letI : MeasurableSpace R := borel R
    letI : BorelSpace R := ⟨rfl⟩
    letI : MeasurableSpace Rᗮ := borel Rᗮ
    letI : BorelSpace Rᗮ := ⟨rfl⟩
    Nontrivial Rᗮ ∧
      ∃ μR : Measure R, ∃ μS : Measure Rᗮ,
        Measure.IsAddHaarMeasure μR ∧ Measure.IsAddHaarMeasure μS := by
  exact SardDerivativeRangeOrthogonalMeasurePackageProbe.exists_range_orthogonal_borel_addHaarMeasure L hL

#print axioms exists_projected_coordinate_measure_data

end SardFiniteOrderProjectedCoordinateMeasureDataProbe
