import ConstructionTargets.SardNonzeroJetDirectionSelection
import ConstructionTargets.SardNonzeroJetScalarSeparation

namespace SardNonzeroSuccessorJetScalarDirectionsProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A nonzero successor-order jet admits a distinguished first direction,
remaining directions, and a scalar component that is nonzero on their `Fin.cons`. -/
theorem exists_firstDirection_tail_scalar_apply_ne_zero
    (f : E → F) (i : ℕ) (x : E)
    (hx : iteratedFDeriv ℝ (i + 1) f x ≠ 0) :
    ∃ (h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ),
      ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0 := by
  obtain ⟨w, hw⟩ :=
    SardNonzeroJetDirectionSelectionProbe.exists_directions_iteratedFDeriv_apply_ne_zero f hx
  obtain ⟨ℓ, hℓ⟩ :=
    SardNonzeroJetScalarSeparationProbe.exists_scalar_component_iteratedFDeriv_apply_ne_zero
      f w hw
  refine ⟨w 0, Fin.tail w, ℓ, ?_⟩
  simpa only [Fin.cons_self_tail] using hℓ

#print axioms exists_firstDirection_tail_scalar_apply_ne_zero
end SardNonzeroSuccessorJetScalarDirectionsProbe
