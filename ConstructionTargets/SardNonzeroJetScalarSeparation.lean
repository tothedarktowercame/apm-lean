import ConstructionTargets.SardNonzeroJetDirectionSelection
import Mathlib.Analysis.InnerProductSpace.Dual

namespace SardNonzeroJetScalarSeparationProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A nonzero vector in a real inner-product space is separated from zero by
a continuous linear functional. -/
theorem exists_continuousLinearMap_apply_ne_zero
    (w : F) (hw : w ≠ 0) :
    ∃ ℓ : F →L[ℝ] ℝ, ℓ w ≠ 0 := by
  refine ⟨innerSL ℝ w, ?_⟩
  simpa [innerSL_apply_apply] using
    ((inner_self_ne_zero (𝕜 := ℝ) (E := F)).mpr hw)

/-- A selected nonzero value of an iterated Fréchet derivative admits a scalar
continuous-linear component that remains nonzero on the selected directions. -/
theorem exists_scalar_component_iteratedFDeriv_apply_ne_zero
    (f : E → F) {i : ℕ} {x : E} (v : Fin i → E)
    (hv : iteratedFDeriv ℝ i f x v ≠ 0) :
    ∃ ℓ : F →L[ℝ] ℝ, ℓ (iteratedFDeriv ℝ i f x v) ≠ 0 :=
  exists_continuousLinearMap_apply_ne_zero _ hv

#print axioms exists_continuousLinearMap_apply_ne_zero
#print axioms exists_scalar_component_iteratedFDeriv_apply_ne_zero
end SardNonzeroJetScalarSeparationProbe
