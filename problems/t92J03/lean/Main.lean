import Mathlib

/-!
# APM t92J03 — Baire category theorem

The countable family is indexed by `ℕ`; openness and density are stated for
each member, and the conclusion concerns their actual set-theoretic
intersection in the given complete metric space.

## Statement repairs

None.

## Encoding questions

None.
-/

theorem apm_t92j03
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {U : ℕ → Set X}
    (hopen : ∀ n, IsOpen (U n))
    (hdense : ∀ n, Dense (U n)) :
    Dense (⋂ n, U n) := by
  exact dense_iInter_of_isOpen_nat hopen hdense
