import Mathlib

namespace SardNonzeroJetDirectionSelectionProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A nonzero continuous multilinear map is nonzero on some tuple of input
directions. -/
theorem exists_directions_apply_ne_zero
    {i : ℕ} (A : E[×i]→L[ℝ] F) (hA : A ≠ 0) :
    ∃ v : Fin i → E, A v ≠ 0 := by
  by_contra h
  push_neg at h
  apply hA
  ext v
  exact h v

/-- At every point of a nonzero `i`th-jet locus, concrete source directions
witness the nonzero iterated Fréchet derivative. -/
theorem exists_directions_iteratedFDeriv_apply_ne_zero
    (f : E → F) {i : ℕ} {x : E}
    (hx : iteratedFDeriv ℝ i f x ≠ 0) :
    ∃ v : Fin i → E, iteratedFDeriv ℝ i f x v ≠ 0 :=
  exists_directions_apply_ne_zero (iteratedFDeriv ℝ i f x) hx

#print axioms exists_directions_apply_ne_zero
#print axioms exists_directions_iteratedFDeriv_apply_ne_zero
end SardNonzeroJetDirectionSelectionProbe
