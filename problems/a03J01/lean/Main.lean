import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a03J01

## Statement repairs

None.

## Encoding notes

The paper's one-based sequence `(E_k)_{k ≥ 1}` is reindexed by `ℕ`. The set of
indices containing a point is counted by `Set.encard`, so infinite multiplicity is
represented honestly by `⊤`; `apmMultiplicitySet E j` is exactly the set `F_j`.
The ambient `ℝ^d` is encoded as `EuclideanSpace ℝ (Fin d)`.
-/

def apmMultiplicitySet {d : ℕ}
    (E : ℕ → Set (EuclideanSpace ℝ (Fin d))) (j : ℕ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | Set.encard {k : ℕ | x ∈ E k} = j}

theorem apm_a03j01
    {d : ℕ}
    (E : ℕ → Set (EuclideanSpace ℝ (Fin d)))
    (A : ENNReal)
    (hE : ∀ k, MeasurableSet (E k))
    (hA : A = ∑' k, volume (E k))
    (hA_finite : A < ⊤) :
    A = ∑' j : ℕ,
      (((j + 1 : ℕ) : ENNReal) * volume (apmMultiplicitySet E (j + 1))) := by
  sorry
