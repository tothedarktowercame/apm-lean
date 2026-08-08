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

open Filter InnerProductSpace
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

/-- The Hilbertian reverse Radon--Riesz implication. The weak hypothesis is
complex-valued; taking real parts gives the norm-square expansion. -/
lemma apm_m02j03_tendsto_of_weak_and_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {x : ℕ → H} {x₀ : H}
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y)))
    (hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖)) :
    Tendsto x atTop (nhds x₀) := by
  have h_inner : Tendsto (fun n => Complex.re (inner ℂ (x n) x₀)) atTop
      (𝓝 (‖x₀‖ ^ 2)) := by
    have hre := Complex.continuous_re.tendsto (inner ℂ x₀ x₀) |>.comp (hweak x₀)
    have heq : Complex.re (inner ℂ x₀ x₀) = ‖x₀‖ ^ 2 := by
      exact @inner_self_eq_norm_sq ℂ _ _ _ _ x₀
    rw [heq] at hre
    exact hre
  have h_norm_sq : Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 (‖x₀‖ ^ 2)) :=
    hnorm.pow 2
  have h_rhs : Tendsto
      (fun n => ‖x n‖ ^ 2 - 2 * Complex.re (inner ℂ (x n) x₀) + ‖x₀‖ ^ 2)
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 2 * Complex.re (inner ℂ (x n) x₀)) atTop
        (𝓝 (2 * ‖x₀‖ ^ 2)) := tendsto_const_nhds.mul h_inner
    have hsub := Tendsto.sub h_norm_sq h2
    have hzero : ‖x₀‖ ^ 2 - 2 * ‖x₀‖ ^ 2 + ‖x₀‖ ^ 2 = (0 : ℝ) := by ring
    rw [← hzero]
    exact Tendsto.add hsub tendsto_const_nhds
  have hsq : Tendsto (fun n => ‖x n - x₀‖ ^ 2) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (norm_sub_sq (𝕜 := ℂ) _ _).symm) h_rhs
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  have hnorm_sub : Tendsto (fun n => ‖x n - x₀‖) atTop (𝓝 0) :=
    hsqrt.congr (fun n => Real.sqrt_sq (norm_nonneg _))
  simpa [tendsto_iff_norm_sub_tendsto_zero] using hnorm_sub

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

  CLOSER HOP 3: the reverse Radon--Riesz prerequisite is now closed by
  `apm_m02j03_tendsto_of_weak_and_norm`. Applying `Complex.continuous_re` to
  `hweak x₀` gives convergence of the real inner products. Together with the
  squared norm limit, `norm_sub_sq (𝕜 := ℂ)` shows
  `‖x n - x₀‖² → 0`; continuity of `Real.sqrt` yields norm convergence of the
  differences and hence strong convergence. This adapts the solved real
  Hilbert-space pattern from `a93A03` to the frozen complex-valued hypothesis.

  Searches beyond hop 2 also covered `a93A03`, Banach--Steinhaus operator
  families, and convex-closure extraction. The solved sibling supplied the
  polarization architecture used above, but no theorem directly converts the
  pointwise raw inner-product hypothesis into a uniform norm bound, and no API
  produces the required strictly-positive triangular coefficients. Those two
  bridges remain open; the frozen statement is unchanged.
  -/
  sorry
