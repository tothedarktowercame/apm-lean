import ConstructionTargets.SardNonsurjectiveDerivativeOrthogonalNontrivial
import ConstructionTargets.SardFiniteDimensionalBorelAddHaarPackage
open MeasureTheory

noncomputable section

namespace SardDerivativeRangeInheritedBorelAddHaarPackageProbe

/-- For a derivative into a Borel finite-dimensional target, the inherited
measurable structures on its range coordinates support additive Haar measures. -/
theorem exists_inherited_range_orthogonal_addHaarMeasure
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L) :
    Nontrivial (LinearMap.range L.toLinearMap)ᗮ ∧
      ∃ μR : Measure (LinearMap.range L.toLinearMap),
      ∃ μS : Measure (LinearMap.range L.toLinearMap)ᗮ,
        Measure.IsAddHaarMeasure μR ∧ Measure.IsAddHaarMeasure μS := by
  letI : Nontrivial (LinearMap.range L.toLinearMap)ᗮ :=
    SardNonsurjectiveDerivativeOrthogonalNontrivialProbe.nontrivial_range_orthogonal_of_not_surjective L hL
  let μR : Measure (LinearMap.range L.toLinearMap) := Measure.addHaar
  let μS : Measure (LinearMap.range L.toLinearMap)ᗮ := Measure.addHaar
  exact ⟨inferInstance, μR, μS, inferInstance, inferInstance⟩

#print axioms exists_inherited_range_orthogonal_addHaarMeasure

end SardDerivativeRangeInheritedBorelAddHaarPackageProbe
