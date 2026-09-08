import ConstructionTargets.SardLowerDimensionalProjectedSliceImageNullity

open Set MeasureTheory

namespace SardProjectedSliceLocalImageNullityWitnessProbe

/-- A local source piece has null image when its image is contained in a
lower-dimensional projected slice whose projected derivative vanishes. -/
theorem local_image_null_of_subset_projectedSlice
    {E F G R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    (μ : Measure F) (n : WithTop ℕ∞)
    (hind : Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ n q z) →
        μ (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (f : E → F) (t U : Set E) (x : E)
    (q : G → F) (s : Set G) (P : F →L[ℝ] R)
    (hopen : IsOpen U) (hx : x ∈ U)
    (hparam : f '' (t ∩ U) ⊆ q '' s)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E)
    (hn : n ≠ 0)
    (hq : ∀ z ∈ s, ContDiffAt ℝ n q z)
    (hP : Function.Surjective P)
    (hzero : ∀ z ∈ s, HasFDerivAt (P ∘ q) (0 : G →L[ℝ] R) z) :
    IsOpen U ∧ x ∈ U ∧ μ (f '' (t ∩ U)) = 0 := by
  refine ⟨hopen, hx, ?_⟩
  apply measure_mono_null hparam
  exact SardLowerDimensionalProjectedSliceImageNullityProbe.image_null_of_lowerDim_projected_derivative_zero
    μ n hind q s P hdim hn hq hP hzero

#print axioms local_image_null_of_subset_projectedSlice
end SardProjectedSliceLocalImageNullityWitnessProbe
