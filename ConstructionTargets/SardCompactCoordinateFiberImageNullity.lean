import ConstructionTargets.SardCompactProductImageFiberNullity
import ConstructionTargets.SardContinuousLinearEquivImageNullity

open Set MeasureTheory

namespace SardCompactCoordinateFiberImageNullityProbe

variable {E F R S : Type*} [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [MeasurableSpace R] [BorelSpace R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [MeasurableSpace S] [BorelSpace S]
  [LocallyCompactSpace S] [SecondCountableTopology S]

/-- A compact image is null when all residual images of its fixed first-coordinate
fibers are null after a continuous-linear product coordinate change. -/
theorem measure_image_zero_of_compact_coordinate_fibers
    (μF : Measure F) (μR : Measure R) (μS : Measure S)
    [Measure.IsAddHaarMeasure μF] [Measure.IsAddHaarMeasure μR]
    [Measure.IsAddHaarMeasure μS]
    (e : F ≃L[ℝ] R × S) (q : E → F) (K : Set E)
    (hK : IsCompact K) (hq : ContinuousOn q K)
    (hfibers : ∀ r,
      μS ((fun x => (e (q x)).2) '' (K ∩ {x | (e (q x)).1 = r})) = 0) :
    μF (q '' K) = 0 := by
  apply SardContinuousLinearEquivImageNullityProbe.ContinuousLinearEquiv.measure_zero_of_image_zero_addHaar
    e μF (μR.prod μS) (q '' K)
  rw [Set.image_image]
  apply SardCompactProductImageFiberNullityProbe.measure_prod_image_zero_of_fstFiber_snd_image_zero
    μR μS (fun x => e (q x)) K hK
  · exact e.continuous.comp_continuousOn hq
  · exact hfibers

#print axioms measure_image_zero_of_compact_coordinate_fibers

end SardCompactCoordinateFiberImageNullityProbe
