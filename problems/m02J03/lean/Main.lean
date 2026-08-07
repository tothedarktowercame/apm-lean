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

/- Strong convergence gives the easy direction of the Radon--Riesz
equivalence.  Keeping it separate isolates the genuinely Hilbertian reverse
direction, which must additionally use `hweak`. -/
lemma apm_m02j03_norm_tendsto_of_tendsto
    {H : Type*} [NormedAddCommGroup H]
    {x : ℕ → H} {x₀ : H}
    (h : Tendsto x atTop (nhds x₀)) :
    Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖) :=
  (continuous_norm.tendsto x₀).comp h

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
  CLOSER HOP 1 (partial). The forward half of the Radon--Riesz equivalence is
  now compiled as `apm_m02j03_norm_tendsto_of_tendsto`; it is just continuity
  of the norm and does not use weak convergence.

  Mathlib provides the central
  separation result `Convex.toWeakSpace_closure`, so the weak limit can in
  principle be moved into the norm closure of a convex hull. However, searches
  found no compiled theorem extracting from that closure a sequence of
  `Fin (n + 1)` convex combinations whose coefficients are all *strictly*
  positive, as required by this statement. The standard convex-hull witness
  permits finite supports and nonnegative coefficients; padding it to every
  initial segment while preserving convergence needs a separate quantitative
  construction.

  Renewed searches of `LEMMA-INDEX.md`, the solved corpus, and Mathlib's weak
  topology / convex-closure sources found no packaged bridge from the frozen
  pointwise inner-product convergence hypothesis to a uniform norm bound, nor
  the required strictly-positive triangular convex-combination sequence. The
  remaining prerequisites are Banach--Steinhaus for the inner-product
  functionals, the Hilbert norm-square identity for the reverse Radon--Riesz
  implication, and the quantitative padding construction. The frozen
  statement is unchanged.
  -/
  sorry
