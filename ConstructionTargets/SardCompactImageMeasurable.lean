import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Set

namespace SardCompactImageMeasurableProbe

/-- The continuous image of a compact localization is Borel measurable in a
Hausdorff Borel target. -/
theorem measurableSet_image_of_isCompact_continuousOn
    {E F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [T2Space F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (hf : ContinuousOn f K) :
    MeasurableSet (f '' K) := by
  exact (hK.image_of_continuousOn hf).isClosed.measurableSet

#print axioms measurableSet_image_of_isCompact_continuousOn
end SardCompactImageMeasurableProbe
