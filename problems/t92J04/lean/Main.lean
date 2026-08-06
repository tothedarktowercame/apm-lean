import Mathlib

/-!
# APM t92J04

## Statement repairs

The standard statement implicitly treats the compact metric space as
nonempty. This is made explicit: for the empty space the empty family is an
open cover, but the requested conclusion cannot choose a member containing
the empty subset.

## Encoding questions

The cover is represented as a set of open subsets whose union is the whole
space. Diameter is Mathlib's metric diameter `Metric.diam`.
-/

open Set

theorem apm_t92j04
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (U : Set (Set X))
    (hU_open : ∀ V ∈ U, IsOpen V)
    (hU_cover : ⋃₀ U = (univ : Set X)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ C : Set X, Metric.diam C < ε → ∃ V ∈ U, C ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric_sUnion
    (s := (univ : Set X)) isCompact_univ hU_open (by simpa [hU_cover])
  refine ⟨ε, hε, ?_⟩
  intro C hdiam
  by_cases hC : C.Nonempty
  · obtain ⟨x, hx⟩ := hC
    obtain ⟨V, hVU, hxV⟩ := hball x (mem_univ x)
    refine ⟨V, hVU, fun y hy => hxV ?_⟩
    have hdist : dist y x ≤ Metric.diam C :=
      Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace hy hx
    exact hdist.trans_lt hdiam
  · obtain ⟨x : X⟩ := ‹Nonempty X›
    obtain ⟨V, hVU, hxV⟩ := hball x (mem_univ x)
    refine ⟨V, hVU, ?_⟩
    simpa [Set.not_nonempty_iff_eq_empty.mp hC]
