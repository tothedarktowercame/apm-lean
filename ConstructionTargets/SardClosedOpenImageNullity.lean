import ConstructionTargets.SardClosedOpenCompactExhaustion

open Set MeasureTheory

namespace SardClosedOpenImageNullityProbe

/-- Memberwise nullity on compact subsets aggregates over a closed locus
localized to an open chart. -/
theorem measure_image_zero_of_closed_inter_open
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace Y]
    (μ : Measure Y) (f : X → Y) (s U : Set X)
    (hs : IsClosed s) (hU : IsOpen U)
    (hnull : ∀ K : Set X, IsCompact K → K ⊆ s ∩ U → μ (f '' K) = 0) :
    μ (f '' (s ∩ U)) = 0 := by
  obtain ⟨K, hK, hcover⟩ :=
    SardClosedOpenCompactExhaustionProbe.exists_compact_cover_inter_of_isClosed_isOpen
      s U hs hU
  apply SardCountableCompactImageNullityProbe.measure_image_zero_of_countable_compact_cover
    μ f (s ∩ U) K hK
  · rw [hcover]
  · intro i
    apply hnull (K i) (hK i)
    rw [← hcover]
    exact subset_iUnion K i

#print axioms measure_image_zero_of_closed_inter_open

end SardClosedOpenImageNullityProbe
