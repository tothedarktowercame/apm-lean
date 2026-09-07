import ConstructionTargets.SardHigherJetLocusDecomposition

open Set

namespace SardNonzeroJetOpenLocusProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Under the exact differentiability-order bound, the locus on which the
`i`th Fréchet derivative is nonzero is open. -/
theorem isOpen_setOf_iteratedFDeriv_ne_zero
    (f : E → F) (n i : ℕ) (hf : ContDiff ℝ n f) (hi : i ≤ n) :
    IsOpen {x | iteratedFDeriv ℝ i f x ≠ 0} := by
  exact (isClosed_singleton.preimage
    (hf.continuous_iteratedFDeriv (mod_cast hi))).isOpen_compl

/-- The nonzero-jet locus inside an arbitrary source set is the restriction of
an open ambient jet locus. -/
theorem nonzeroJetLocus_eq_inter_open
    (f : E → F) (K : Set E) (n i : ℕ) (hf : ContDiff ℝ n f) (hi : i ≤ n) :
    ∃ U : Set E, IsOpen U ∧
      SardHigherJetLocusDecompositionProbe.nonzeroJetLocus f K i = K ∩ U := by
  refine ⟨{x | iteratedFDeriv ℝ i f x ≠ 0},
    isOpen_setOf_iteratedFDeriv_ne_zero f n i hf hi, ?_⟩
  rfl

#print axioms isOpen_setOf_iteratedFDeriv_ne_zero
#print axioms nonzeroJetLocus_eq_inter_open
end SardNonzeroJetOpenLocusProbe
