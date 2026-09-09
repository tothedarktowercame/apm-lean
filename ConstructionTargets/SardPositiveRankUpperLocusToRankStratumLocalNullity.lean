import ConstructionTargets.SardFiniteOrderPositiveRankPointwiseNullity
import ConstructionTargets.SardExactRankLocalUpperLocus

open Set MeasureTheory

namespace SardPositiveRankUpperLocusToRankStratumLocalNullityProbe

theorem exists_open_rankStratum_image_zero_of_rankUpper
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (x : E) (r : ℕ)
    (U V rankUpper : Set E)
    (hU : IsOpen U) (hxU : x ∈ U)
    (hV : IsOpen V) (hxV : x ∈ V)
    (heq : U ∩ rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r = U ∩ rankUpper)
    (hzero : μ (f '' (rankUpper ∩ V)) = 0) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧
      μ (f '' (rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r ∩ W)) = 0 := by
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  apply measure_mono_null (t := f '' (rankUpper ∩ V)) ?_ hzero
  rintro y ⟨z, ⟨hzrank, hzU, hzV⟩, rfl⟩
  refine ⟨z, ⟨?_, hzV⟩, rfl⟩
  have : z ∈ U ∩ rankUpper := heq ▸ ⟨hzU, hzrank⟩
  exact this.2

#print axioms exists_open_rankStratum_image_zero_of_rankUpper

end SardPositiveRankUpperLocusToRankStratumLocalNullityProbe
