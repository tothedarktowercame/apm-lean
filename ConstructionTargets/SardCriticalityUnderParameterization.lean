import ConstructionTargets.SardImplicitFunctionKernelParameterCompositionContDiff

namespace SardCriticalityUnderParameterizationProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Nonsurjectivity is preserved by precomposition with an arbitrary
continuous linear map. -/
theorem ContinuousLinearMap.not_surjective_comp_of_not_surjective
    (A : E →L[ℝ] F) (B : G →L[ℝ] E) (hA : ¬ Function.Surjective A) :
    ¬ Function.Surjective (A.comp B) := by
  intro hAB
  apply hA
  intro y
  obtain ⟨x, hx⟩ := hAB y
  exact ⟨B x, hx⟩

/-- The chain rule transports a derivative-critical point to every smooth
parameterization of its source. -/
theorem HasFDerivAt.comp_and_not_surjective
    {f : E → F} {g : G → E} {x : G} {A : E →L[ℝ] F} {B : G →L[ℝ] E}
    (hf : HasFDerivAt f A (g x)) (hg : HasFDerivAt g B x)
    (hA : ¬ Function.Surjective A) :
    HasFDerivAt (fun z => f (g z)) (A.comp B) x ∧
      ¬ Function.Surjective (A.comp B) := by
  exact ⟨hf.comp x hg,
    ContinuousLinearMap.not_surjective_comp_of_not_surjective A B hA⟩

#print axioms ContinuousLinearMap.not_surjective_comp_of_not_surjective
#print axioms HasFDerivAt.comp_and_not_surjective
end SardCriticalityUnderParameterizationProbe
