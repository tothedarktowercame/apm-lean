import ConstructionTargets.SardParameterizedCriticalImageNullity
import Mathlib.Topology.Compactness.Lindelof

open Set MeasureTheory

namespace SardLocalNullitySecondCountableAggregationProbe

/-- In a second-countable source, pointwise open neighborhoods with null
restricted images aggregate to a null image of the whole source set. -/
theorem image_null_of_locally_image_null
    {E F : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [MeasurableSpace F] (μ : Measure F) (f : E → F) (s : Set E)
    (U : E → Set E)
    (hopen : ∀ x ∈ s, IsOpen (U x))
    (hmem : ∀ x ∈ s, x ∈ U x)
    (hnull : ∀ x ∈ s, μ (f '' (s ∩ U x)) = 0) :
    μ (f '' s) = 0 := by
  obtain ⟨c, hc_count, hc_cover⟩ :=
    (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
      (fun x : s => U x) (fun x => hopen x x.property) (by
        intro x hx
        exact mem_iUnion.2 ⟨⟨x, hx⟩, hmem x hx⟩)
  letI : Countable c := hc_count.to_subtype
  apply measure_mono_null (t := ⋃ x : c, f '' (s ∩ U x.1.1))
  · rintro y ⟨x, hx, rfl⟩
    have hxU := hc_cover hx
    simp only [mem_iUnion] at hxU
    obtain ⟨z, hzc, hxUz⟩ := hxU
    exact mem_iUnion_of_mem (⟨z, hzc⟩ : c) ⟨x, ⟨hx, hxUz⟩, rfl⟩
  · exact measure_iUnion_null fun x => hnull x.1.1 x.1.2

#print axioms image_null_of_locally_image_null
end SardLocalNullitySecondCountableAggregationProbe
