import Mathlib

/-!
# APM t92J04

## Statement repairs

None.

## Encoding questions

The cover is represented as a set of open subsets whose union is the whole
space. Diameter is Mathlib's metric diameter `Metric.diam`.
-/

open Set

theorem apm_t92j04
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (U : Set (Set X))
    (hU_open : ∀ V ∈ U, IsOpen V)
    (hU_cover : ⋃₀ U = (univ : Set X)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ C : Set X, Metric.diam C < ε → ∃ V ∈ U, C ⊆ V := by
  sorry
