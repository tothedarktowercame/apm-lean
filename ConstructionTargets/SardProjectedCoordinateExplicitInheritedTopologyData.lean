import ConstructionTargets.SardFiniteOrderPointwiseWitnessExplicitMeasurableSpaces

namespace SardProjectedCoordinateExplicitInheritedTopologyDataProbe

theorem exists_projectedCoordinates_explicit_inherited_topologyData
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) :
    Nonempty (LocallyCompactSpace (LinearMap.range L.toLinearMap)) ∧
      Nonempty (SecondCountableTopology (LinearMap.range L.toLinearMap)) ∧
      Nonempty (LocallyCompactSpace (LinearMap.range L.toLinearMap)ᗮ) ∧
      Nonempty (SecondCountableTopology (LinearMap.range L.toLinearMap)ᗮ) := by
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

#print axioms exists_projectedCoordinates_explicit_inherited_topologyData

end SardProjectedCoordinateExplicitInheritedTopologyDataProbe
