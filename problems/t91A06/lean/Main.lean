import Mathlib

/-!
# APM t91A06 — compact Hausdorff spaces are Baire

## Statement repairs

None.
-/

theorem apm_t91a06
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (U : ℕ → Set X) (hopen : ∀ i, IsOpen (U i))
    (hdense : ∀ i, Dense (U i)) :
    Dense (⋂ i, U i) := by
  sorry
