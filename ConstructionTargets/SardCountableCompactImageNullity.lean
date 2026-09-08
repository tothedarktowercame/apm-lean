import ConstructionTargets.SardCompactTargetFiberProjectedSliceImageNullity

open Set MeasureTheory

namespace SardCountableCompactImageNullityProbe

/-- Null images of a countable compact cover aggregate to nullity of the
image of the covered source set. -/
theorem measure_image_zero_of_countable_compact_cover
    {X Y ι : Type*} [TopologicalSpace X] [Countable ι] [MeasurableSpace Y]
    (μ : Measure Y) (f : X → Y) (s : Set X) (K : ι → Set X)
    (_hcompact : ∀ i, IsCompact (K i))
    (hcover : s ⊆ ⋃ i, K i)
    (hnull : ∀ i, μ (f '' K i) = 0) :
    μ (f '' s) = 0 := by
  apply measure_mono_null (t := ⋃ i, f '' K i)
  · rintro y ⟨x, hx, rfl⟩
    rcases mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    exact mem_iUnion_of_mem i ⟨x, hxi, rfl⟩
  · exact measure_iUnion_null hnull

#print axioms measure_image_zero_of_countable_compact_cover

end SardCountableCompactImageNullityProbe
