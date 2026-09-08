import ConstructionTargets.SardLowerDimensionalLocalCriticalImageInduction
import ConstructionTargets.SardProjectedSliceDerivativeNonsurjective

open Set MeasureTheory

namespace SardLowerDimensionalProjectedSliceImageNullityProbe

/-- Lower-dimensional Sard induction applies to an entire slice when a
surjective projected coordinate has zero derivative at every slice point. -/
theorem image_null_of_lowerDim_projected_derivative_zero
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
    (q : G → F) (s : Set G) (P : F →L[ℝ] R)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E)
    (hn : n ≠ 0)
    (hq : ∀ z ∈ s, ContDiffAt ℝ n q z)
    (hP : Function.Surjective P)
    (hzero : ∀ z ∈ s, HasFDerivAt (P ∘ q) (0 : G →L[ℝ] R) z) :
    μ (q '' s) = 0 := by
  have hcritical : s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)} = s := by
    ext z
    constructor
    · exact fun hz => hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      have hqd : DifferentiableAt ℝ q z := (hq z hz).differentiableAt hn
      exact SardProjectedSliceDerivativeNonsurjectiveProbe.not_surjective_fderiv_of_projected_hasFDerivAt_zero
        q z (fderiv ℝ q z) P hqd.hasFDerivAt hP (hzero z hz)
  rw [← hcritical]
  exact hind hdim q s hq

#print axioms image_null_of_lowerDim_projected_derivative_zero
end SardLowerDimensionalProjectedSliceImageNullityProbe
