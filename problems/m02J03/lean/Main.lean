import Mathlib

/-!
# APM m02J03

## Statement repairs

None.

## Encoding notes

The source indices start at one.  Lean's sequence starts at zero, so the
`n`th convex combination is indexed by `Fin (n + 1)` and uses exactly
`x 0, …, x n`.  The coefficients remain real, strictly positive, and sum to
one as required.
-/

open Filter
open scoped BigOperators Topology

theorem apm_m02j03
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y))) :
    (∃ C : ℝ, ∀ n : ℕ, ‖x n‖ ≤ C) ∧
    (Tendsto x atTop (nhds x₀) ↔
      Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖)) ∧
    ∃ α : ∀ n : ℕ, Fin (n + 1) → ℝ,
      (∀ n : ℕ, (∀ i : Fin (n + 1), 0 < α n i) ∧ ∑ i, α n i = 1) ∧
      Tendsto (fun n ↦ ∑ i : Fin (n + 1), (α n i : ℂ) • x i.val)
        atTop (nhds x₀) := by
  /-
  SKIPPED (Mazur/triangular-coefficient bridge). Mathlib provides the central
  separation result `Convex.toWeakSpace_closure`, so the weak limit can in
  principle be moved into the norm closure of a convex hull. However, searches
  found no compiled theorem extracting from that closure a sequence of
  `Fin (n + 1)` convex combinations whose coefficients are all *strictly*
  positive, as required by this statement. The standard convex-hull witness
  permits finite supports and nonnegative coefficients; padding it to every
  initial segment while preserving convergence needs a separate quantitative
  construction.

  The other prerequisites also require assembling Banach–Steinhaus for the
  inner-product functionals and the Hilbert norm-square identity for the
  Radon–Riesz implication. No solved sibling contains this combined route. The
  available weak-closure theorem was therefore insufficient for a bounded
  pass-1 proof; no sibling code was reused and the frozen statement was left
  unchanged.
  -/
  sorry
