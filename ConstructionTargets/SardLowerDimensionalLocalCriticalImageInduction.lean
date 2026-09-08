import ConstructionTargets.SardParameterizedLocalCriticalImageNullity

open Set MeasureTheory

namespace SardLowerDimensionalLocalCriticalImageInductionProbe

/-- A source-dimension induction hypothesis applies to a smooth local parameterization,
and its local critical-image conclusion transfers back to the original critical set. -/
theorem localizedCriticalImage_null_of_lowerDim_parameterization
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (μ : Measure F) (n : WithTop ℕ∞)
    (hind : Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ n q z) →
        μ (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (f : E → F) (g : G → E) (s : Set G) (t : Set E)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E)
    (hn : n ≠ 0)
    (hparam : t ⊆ g '' s)
    (hf : ∀ z ∈ s, ContDiffAt ℝ n f (g z))
    (hg : ∀ z ∈ s, ContDiffAt ℝ n g z)
    (htcrit : ∀ x ∈ t, ¬ Function.Surjective (fderiv ℝ f x)) :
    μ (f '' t) = 0 := by
  apply SardParameterizedLocalCriticalImageNullityProbe.localizedCriticalImage_null_of_parameterized_on
    μ f g s t hparam
  · intro z hz
    exact (hf z hz).differentiableAt hn
  · intro z hz
    exact (hg z hz).differentiableAt hn
  · exact htcrit
  · apply hind hdim (f ∘ g) s
    intro z hz
    exact (hf z hz).comp z (hg z hz)

#print axioms localizedCriticalImage_null_of_lowerDim_parameterization

end SardLowerDimensionalLocalCriticalImageInductionProbe
