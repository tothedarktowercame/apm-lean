import Mathlib.MeasureTheory.Measure.Prod

open Set MeasureTheory

namespace SardProductNullityOfNullFibersProbe

/-- A measurable set in a product has zero product measure when every vertical
section has zero measure. -/
theorem measure_prod_zero_of_forall_fiber_zero
    {R S : Type*} [MeasurableSpace R] [MeasurableSpace S]
    (μ : Measure R) (ν : Measure S) (A : Set (R × S))
    (hA : MeasurableSet A)
    (hsections : ∀ r, ν (Prod.mk r ⁻¹' A) = 0) :
    μ.prod ν A = 0 := by
  apply Measure.measure_prod_null_of_ae_null hA
  filter_upwards [] with r
  exact hsections r

#print axioms measure_prod_zero_of_forall_fiber_zero
end SardProductNullityOfNullFibersProbe
