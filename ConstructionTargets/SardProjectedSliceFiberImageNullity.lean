import ConstructionTargets.SardLowerDimensionalProjectedSliceImageNullity

open Set MeasureTheory

namespace SardProjectedSliceFiberImageNullityProbe

/-- Fixed-coordinate residual fiber images are null when they are contained in
lower-dimensional projected slices satisfying the Sard induction hypotheses. -/
theorem forall_fiber_image_null_of_subset_projectedSlices
    {E F G R A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    (μ : Measure F) (n : WithTop ℕ∞)
    (hind : Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ n q z) →
        μ (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (a : A → E) (b : A → F) (K : Set A)
    (q : E → G → F) (s : E → Set G) (P : F →L[ℝ] R)
    (hparam : ∀ r, b '' (K ∩ {x | a x = r}) ⊆ q r '' s r)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E)
    (hn : n ≠ 0)
    (hq : ∀ r z, z ∈ s r → ContDiffAt ℝ n (q r) z)
    (hP : Function.Surjective P)
    (hzero : ∀ r z, z ∈ s r → HasFDerivAt (P ∘ q r) (0 : G →L[ℝ] R) z) :
    ∀ r, μ (b '' (K ∩ {x | a x = r})) = 0 := by
  intro r
  apply measure_mono_null (hparam r)
  exact SardLowerDimensionalProjectedSliceImageNullityProbe.image_null_of_lowerDim_projected_derivative_zero
    μ n hind (q r) (s r) P hdim hn (hq r) hP (hzero r)

#print axioms forall_fiber_image_null_of_subset_projectedSlices

end SardProjectedSliceFiberImageNullityProbe
