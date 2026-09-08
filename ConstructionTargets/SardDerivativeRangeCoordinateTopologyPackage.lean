import ConstructionTargets.SardDerivativeRangeInheritedBorelSpace

namespace SardDerivativeRangeCoordinateTopologyPackageProbe

/-- Finite-dimensional derivative-range coordinates are proper and
second-countable, hence locally compact through the proper-space instance. -/
theorem range_orthogonal_topology_package
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) :
    ProperSpace (LinearMap.range L.toLinearMap) ∧
      SecondCountableTopology (LinearMap.range L.toLinearMap) ∧
      ProperSpace (LinearMap.range L.toLinearMap)ᗮ ∧
      SecondCountableTopology (LinearMap.range L.toLinearMap)ᗮ := by
  letI : ProperSpace (LinearMap.range L.toLinearMap) :=
    FiniteDimensional.proper ℝ (LinearMap.range L.toLinearMap)
  letI : ProperSpace (LinearMap.range L.toLinearMap)ᗮ :=
    FiniteDimensional.proper ℝ (LinearMap.range L.toLinearMap)ᗮ
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

#print axioms range_orthogonal_topology_package

end SardDerivativeRangeCoordinateTopologyPackageProbe
