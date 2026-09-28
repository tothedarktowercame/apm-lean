import Mathlib

/-! Here a Cantor subset means a subset homeomorphic to Cantor space
`ℕ → Bool`; this fixes the standard topological meaning without introducing
an uninterpreted predicate. -/

def apm_t94a03_IsCantorSet (C : Set ℝ) : Prop :=
  Nonempty ((ℕ → Bool) ≃ₜ C)

lemma cantor_isClosed {C : Set ℝ} (h : apm_t94a03_IsCantorSet C) : IsClosed C := by
  obtain ⟨e⟩ := h
  have : CompactSpace C := e.compactSpace
  exact (isCompact_iff_compactSpace.2 this).isClosed

lemma cantor_interior_empty {C : Set ℝ} (h : apm_t94a03_IsCantorSet C) : interior C = ∅ := by
  obtain ⟨e⟩ := h
  have : TotallyDisconnectedSpace C := e.totallyDisconnectedSpace
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hsub : Set.Ioo (x - ε) (x + ε) ⊆ C := by
    intro y hy; apply interior_subset; apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
  have htd : IsTotallyDisconnected C := totallyDisconnectedSpace_subtype_iff.1 this
  have := htd _ hsub isPreconnected_Ioo
  have h1 : x ∈ Set.Ioo (x - ε) (x + ε) := ⟨by linarith, by linarith⟩
  have h2 : x + ε/2 ∈ Set.Ioo (x - ε) (x + ε) := ⟨by linarith, by linarith⟩
  have := this h1 h2
  linarith

/-- The real line is not a countable union of Cantor sets. -/
theorem apm_t94a03 :
    ¬ ∃ C : ℕ → Set ℝ,
      (∀ n, apm_t94a03_IsCantorSet (C n)) ∧
        ⋃ n, C n = Set.univ := by
  rintro ⟨C, hC, hU⟩
  have := nonempty_interior_of_iUnion_of_closed (fun n => cantor_isClosed (hC n)) hU
  obtain ⟨n, hn⟩ := this
  rw [cantor_interior_empty (hC n)] at hn
  exact Set.not_nonempty_empty hn
