import ConstructionTargets.SardAffineLineTaylorRemainder

open Set

/-- A continuously differentiable map has a single nonnegative bound for the
norm of its fixed-order iterated Fréchet derivative on a compact set. -/
theorem exists_nonneg_norm_iteratedFDeriv_le_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (n m : ℕ)
    (hf : ContDiff ℝ n f) (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ m f x‖ ≤ C := by
  have hc : Continuous (fun x => ‖iteratedFDeriv ℝ m f x‖) :=
    continuous_norm.comp (hf.continuous_iteratedFDeriv (mod_cast hm))
  obtain ⟨M, hM⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hM (mem_image_of_mem _ hx)).trans (le_max_left _ _)

#print axioms exists_nonneg_norm_iteratedFDeriv_le_on_compact
