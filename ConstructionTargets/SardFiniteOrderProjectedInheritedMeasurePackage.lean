import ConstructionTargets.SardProjectedCoordinateInheritedBorelBridge
import ConstructionTargets.SardDerivativeRangeInheritedBorelAddHaarPackage

open MeasureTheory

noncomputable section

namespace SardFiniteOrderProjectedInheritedMeasurePackageProbe

/-- The projected coordinates retain their inherited measurable spaces while
carrying the Borel and additive-Haar data used by the local nullity theorem. -/
theorem exists_projected_inherited_borel_addHaar_data
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L) :
    (BorelSpace (LinearMap.range L.toLinearMap) ∧
      BorelSpace (LinearMap.range L.toLinearMap)ᗮ) ∧
      Nontrivial (LinearMap.range L.toLinearMap)ᗮ ∧
      ∃ μR : Measure (LinearMap.range L.toLinearMap),
      ∃ μS : Measure (LinearMap.range L.toLinearMap)ᗮ,
        Measure.IsAddHaarMeasure μR ∧ Measure.IsAddHaarMeasure μS := by
  exact ⟨
    SardProjectedCoordinateInheritedBorelBridgeProbe.projectedCoordinates_inherited_borelSpace L,
    SardDerivativeRangeInheritedBorelAddHaarPackageProbe.exists_inherited_range_orthogonal_addHaarMeasure L hL⟩

#print axioms exists_projected_inherited_borel_addHaar_data

end SardFiniteOrderProjectedInheritedMeasurePackageProbe
