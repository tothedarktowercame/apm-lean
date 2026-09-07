import ConstructionTargets.SardCriticalityUnderParameterization

namespace SardCriticalSetUnderParameterizationProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A point whose derivative is nonsurjective remains derivative-critical
after any differentiable parameterization of the source. -/
theorem not_surjective_fderiv_comp
    {f : E → F} {g : G → E} {x : G}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x)
    (hcrit : ¬ Function.Surjective (fderiv ℝ f (g x))) :
    ¬ Function.Surjective (fderiv ℝ (f ∘ g) x) := by
  rw [fderiv_comp x hf hg]
  exact SardCriticalityUnderParameterizationProbe.ContinuousLinearMap.not_surjective_comp_of_not_surjective
    (fderiv ℝ f (g x)) (fderiv ℝ g x) hcrit

/-- Set-level form of criticality transport for a differentiable
parameterization. -/
theorem preimage_criticalSet_subset_criticalSet_comp
    (f : E → F) (g : G → E) (s : Set G)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f (g x))
    (hg : ∀ x ∈ s, DifferentiableAt ℝ g x) :
    s ∩ g ⁻¹' {y | ¬ Function.Surjective (fderiv ℝ f y)} ⊆
      {x | ¬ Function.Surjective (fderiv ℝ (f ∘ g) x)} := by
  rintro x ⟨hxs, hxcrit⟩
  exact not_surjective_fderiv_comp (hf x hxs) (hg x hxs) hxcrit

#print axioms not_surjective_fderiv_comp
#print axioms preimage_criticalSet_subset_criticalSet_comp
end SardCriticalSetUnderParameterizationProbe
