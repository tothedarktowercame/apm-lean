import ConstructionTargets.SardLowerDimensionalProjectedSliceImageNullity

open Set MeasureTheory

namespace SardProjectedSliceFiberImageNullityIndexedProbe

/-- Fixed-coordinate residual fiber images are null when the coordinate index
and the ambient source used for the Sard dimension inequality are independent. -/
theorem forall_fiber_image_null_of_subset_projectedSlices_indexed
    {D F G R A C : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    (μ : Measure F) (n : WithTop ℕ∞)
    (hind : Module.finrank ℝ G < Module.finrank ℝ D →
      ∀ (q : G → F) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ n q z) →
        μ (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (a : A → C) (b : A → F) (K : Set A)
    (q : C → G → F) (s : C → Set G) (P : F →L[ℝ] R)
    (hparam : ∀ r, b '' (K ∩ {x | a x = r}) ⊆ q r '' s r)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ D)
    (hn : n ≠ 0)
    (hq : ∀ r z, z ∈ s r → ContDiffAt ℝ n (q r) z)
    (hP : Function.Surjective P)
    (hzero : ∀ r z, z ∈ s r → HasFDerivAt (P ∘ q r) (0 : G →L[ℝ] R) z) :
    ∀ r, μ (b '' (K ∩ {x | a x = r})) = 0 := by
  intro r
  apply measure_mono_null (hparam r)
  exact SardLowerDimensionalProjectedSliceImageNullityProbe.image_null_of_lowerDim_projected_derivative_zero
    μ n hind (q r) (s r) P hdim hn (hq r) hP (hzero r)

#print axioms forall_fiber_image_null_of_subset_projectedSlices_indexed

end SardProjectedSliceFiberImageNullityIndexedProbe
