import ConstructionTargets.SardCompactProductImageNullity
import ConstructionTargets.SardProductImageVerticalSection

open Set MeasureTheory

namespace SardCompactProductImageFiberNullityProbe

/-- A compact continuous product-coordinate image is product-null when the
second-coordinate image of every fixed-first-coordinate source fiber is null. -/
theorem measure_prod_image_zero_of_fstFiber_snd_image_zero
    {E R S : Type*} [TopologicalSpace E]
    [TopologicalSpace R] [T2Space R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R]
    [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S]
    (μ : Measure R) (ν : Measure S) (q : E → R × S) (K : Set E)
    (hK : IsCompact K) (hq : ContinuousOn q K)
    (hfibers : ∀ r,
      ν ((fun x => (q x).2) '' (K ∩ {x | (q x).1 = r})) = 0) :
    μ.prod ν (q '' K) = 0 := by
  apply SardCompactProductImageNullityProbe.measure_prod_image_zero_of_isCompact_continuousOn_of_fibers
    μ ν q K hK hq
  intro r
  rw [SardProductImageVerticalSectionProbe.prodMk_preimage_image_eq_snd_image_fstFiber]
  exact hfibers r

#print axioms measure_prod_image_zero_of_fstFiber_snd_image_zero
end SardCompactProductImageFiberNullityProbe
