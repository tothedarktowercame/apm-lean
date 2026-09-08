import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

open Set MeasureTheory

namespace SardEquivImageNullityTransferProbe

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A quasi-measure-preserving equivalence reflects nullity of an image back
to the original set. -/
theorem measure_zero_of_equiv_image_zero
    (μ : Measure X) (ν : Measure Y) (e : X ≃ Y)
    (he : Measure.QuasiMeasurePreserving (e : X → Y) μ ν)
    (s : Set X) (hs : ν (e '' s) = 0) :
    μ s = 0 := by
  have hpre : μ (e ⁻¹' (e '' s)) = 0 := he.preimage_null hs
  simpa [Set.preimage_image_eq s e.injective] using hpre

#print axioms measure_zero_of_equiv_image_zero

end SardEquivImageNullityTransferProbe
