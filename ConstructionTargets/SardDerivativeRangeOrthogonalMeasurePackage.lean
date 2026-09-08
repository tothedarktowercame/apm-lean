import ConstructionTargets.SardNonsurjectiveDerivativeOrthogonalNontrivial
import ConstructionTargets.SardFiniteDimensionalBorelAddHaarPackage

open MeasureTheory

namespace SardDerivativeRangeOrthogonalMeasurePackageProbe

/-- A nonsurjective derivative supplies Borel additive-Haar packages on its
range and orthogonal residual, together with residual nontriviality. -/
theorem exists_range_orthogonal_borel_addHaarMeasure
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
  let R := LinearMap.range L.toLinearMap
  letI : MeasurableSpace R := borel R
  letI : BorelSpace R := ⟨rfl⟩
  letI : MeasurableSpace Rᗮ := borel Rᗮ
  letI : BorelSpace Rᗮ := ⟨rfl⟩
  let hnontrivial :=
    SardNonsurjectiveDerivativeOrthogonalNontrivialProbe.nontrivial_range_orthogonal_of_not_surjective L hL
  obtain ⟨μR, hμR⟩ :=
    SardFiniteDimensionalBorelAddHaarPackageProbe.exists_borel_addHaarMeasure R
  obtain ⟨μS, hμS⟩ :=
    SardFiniteDimensionalBorelAddHaarPackageProbe.exists_borel_addHaarMeasure Rᗮ
  exact ⟨hnontrivial, μR, μS, hμR, hμS⟩

#print axioms exists_range_orthogonal_borel_addHaarMeasure

end SardDerivativeRangeOrthogonalMeasurePackageProbe
