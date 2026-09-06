import Mathlib

/-! Here a Cantor subset means a subset homeomorphic to Cantor space
`ℕ → Bool`; this fixes the standard topological meaning without introducing
an uninterpreted predicate. -/

def apm_t94a03_IsCantorSet (C : Set ℝ) : Prop :=
  Nonempty ((ℕ → Bool) ≃ₜ C)

/-- The real line is not a countable union of Cantor sets. -/
theorem apm_t94a03 :
    ¬ ∃ C : ℕ → Set ℝ,
      (∀ n, apm_t94a03_IsCantorSet (C n)) ∧
        ⋃ n, C n = Set.univ := by
  sorry
