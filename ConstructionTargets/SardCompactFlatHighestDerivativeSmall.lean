import Mathlib

open Metric Set

theorem exists_uniform_small_iteratedFDeriv_near_compact_flat
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (n : ℕ)
    (hf : ContDiff ℝ n f)
    (hzero : ∀ a ∈ K, iteratedFDeriv ℝ n f a = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ K, ∀ y : E, dist y a < δ →
      ‖iteratedFDeriv ℝ n f y‖ < ε := by
  have hopen : IsOpen {y : E | ‖iteratedFDeriv ℝ n f y‖ < ε} :=
    isOpen_lt hf.continuous_iteratedFDeriv'.norm continuous_const
  have hsub : K ⊆ {y : E | ‖iteratedFDeriv ℝ n f y‖ < ε} := by
    intro a ha
    simpa [hzero a ha] using hε
  obtain ⟨δ, hδ, hnear⟩ := hK.exists_thickening_subset_open hopen hsub
  refine ⟨δ, hδ, ?_⟩
  intro a ha y hy
  exact hnear (mem_thickening_iff.2 ⟨a, ha, hy⟩)

#print axioms exists_uniform_small_iteratedFDeriv_near_compact_flat
