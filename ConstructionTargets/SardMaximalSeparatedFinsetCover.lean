import Mathlib.Topology.MetricSpace.CoveringNumbers

/-! # Maximal separated covers represented as finsets -/

open Metric Set
open scoped ENNReal NNReal

/-- When the packing number is not infinite, Mathlib's maximal separated set
can be represented by a `Finset` while preserving containment, separation, and
covering. -/
theorem exists_finset_maximal_separated_cover
    {X : Type*} [PseudoEMetricSpace X]
    {A : Set X} (ε : ℝ≥0) (hpack : packingNumber ε A ≠ ⊤) :
    ∃ C : Finset X, (↑C : Set X) ⊆ A ∧
      IsSeparated ε (↑C : Set X) ∧ IsCover ε A (↑C : Set X) := by
  have hfinite : (maximalSeparatedSet ε A).Finite := by
    rw [← encard_ne_top_iff, encard_maximalSeparatedSet hpack]
    exact hpack
  refine ⟨hfinite.toFinset, ?_, ?_, ?_⟩
  · simpa using maximalSeparatedSet_subset (ε := ε) (A := A)
  · simpa using isSeparated_maximalSeparatedSet (ε := ε) (A := A)
  · simpa using isCover_maximalSeparatedSet (ε := ε) (A := A) hpack

#print axioms exists_finset_maximal_separated_cover
