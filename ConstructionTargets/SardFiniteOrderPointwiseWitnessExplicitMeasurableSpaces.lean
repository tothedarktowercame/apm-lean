import ConstructionTargets.SardFiniteOrderPointwiseRankChartNullityWitness
import ConstructionTargets.SardProjectedCoordinateExplicitInheritedBorelData

namespace SardFiniteOrderPointwiseWitnessExplicitMeasurableSpacesProbe

theorem projectedCoordinates_explicit_measurableSpace_borel_bindings
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) :
    let mC : MeasurableSpace (LinearMap.range L.toLinearMap) := inferInstance
    let mS : MeasurableSpace (LinearMap.range L.toLinearMap)ᗮ := inferInstance
    @BorelSpace (LinearMap.range L.toLinearMap) inferInstance mC ∧
      @BorelSpace (LinearMap.range L.toLinearMap)ᗮ inferInstance mS := by
  exact SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L

#print axioms projectedCoordinates_explicit_measurableSpace_borel_bindings

end SardFiniteOrderPointwiseWitnessExplicitMeasurableSpacesProbe
