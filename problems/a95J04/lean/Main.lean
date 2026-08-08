import Mathlib

/-!
# APM a95J04 — meromorphic continuation past a circle of convergence

## Statement repairs

None.

## Encoding questions

None. The extension uses Mathlib's genuine `MeromorphicOn` predicate and its
integer-valued `meromorphicOrderAt`; a pole is an order strictly below zero
and a simple pole has order `-1`. The coefficient sequence is pinned to `f`
by the power-series sum on the unit disk. Radius exactly one is expressed by
absolute convergence at every nonnegative radius below one and failure of
absolute convergence at every radius above one.
-/

open Complex Metric Set Filter
open scoped Topology

noncomputable section

/-- A pole of `f` in the closed unit disk must lie on its boundary when `f`
is holomorphic in the open disk.  This isolates the geometric reduction used
by both parts of the theorem. -/
lemma apm_a95J04_pole_mem_sphere_of_mem_closedBall
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hz : z ∈ closedBall (0 : ℂ) 1)
    (hpole : meromorphicOrderAt f z < 0) :
    z ∈ sphere (0 : ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right] at hz
  rw [mem_sphere, dist_zero_right]
  apply le_antisymm hz
  by_contra hnot
  have hzball : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right]
    exact not_le.mp hnot
  have han : AnalyticAt ℂ f z := hf.analyticAt (isOpen_ball.mem_nhds hzball)
  exact (not_lt_of_ge han.meromorphicOrderAt_nonneg) hpole

/-- Meromorphy makes the boundary-pole set finite.  Restricting the locally
finite divisor to the compact unit sphere exposes this directly through
`locallyFinsuppWithin.finiteSupport`. -/
lemma apm_a95J04_boundary_poles_finite
    {D : Set ℂ} (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ} (hmero : MeromorphicOn f D) :
    {z : ℂ | z ∈ sphere (0 : ℂ) 1 ∧ meromorphicOrderAt f z < 0}.Finite := by
  let div := MeromorphicOn.divisor f D
  have hsD : sphere (0 : ℂ) 1 ⊆ D :=
    sphere_subset_closedBall.trans hDcontains
  let ds := div.restrict hsD
  apply (ds.finiteSupport (isCompact_sphere (0 : ℂ) 1)).subset
  intro z hz
  change ds z ≠ 0
  rw [Function.locallyFinsuppWithin.restrict_apply]
  simp only [hz.1, if_true, div, MeromorphicOn.divisor_apply hmero (hsD hz.1)]
  intro hzero
  rw [WithTop.untop₀_eq_zero] at hzero
  rcases hzero with hzero | htop
  · exact (not_lt_of_ge (by rw [hzero])) hz.2
  · exact (not_lt_of_ge (by rw [htop]; exact le_top)) hz.2

theorem apm_a95j04
    (D : Set ℂ) (hDopen : IsOpen D) (hDconn : IsConnected D)
    (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (a : ℕ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hseries : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n ↦ a n * z ^ n) (f z))
    (hradius_lt : ∀ r : ℝ, 0 ≤ r → r < 1 →
      Summable (fun n ↦ ‖a n‖ * r ^ n))
    (hradius_gt : ∀ r : ℝ, 1 < r →
      ¬Summable (fun n ↦ ‖a n‖ * r ^ n))
    (hmero : MeromorphicOn f D) :
    (∃ ζ ∈ sphere (0 : ℂ) 1, meromorphicOrderAt f ζ < 0) ∧
    ((∀ ζ ∈ sphere (0 : ℂ) 1,
        meromorphicOrderAt f ζ < 0 → meromorphicOrderAt f ζ = (-1 : ℤ)) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖a n‖ ≤ M) := by
  /-
  CLOSER HOP 2 (2026-08-08): the new compiled lemma
  `apm_a95J04_pole_mem_sphere_of_mem_closedBall` proves that every pole in
  the closed unit disk is necessarily a boundary pole.  It uses Mathlib's
  previously missed `AnalyticAt.meromorphicOrderAt_nonneg`, so no normal-form
  conversion is needed for this localization.

  I also inspected the repaired exact proof history, `a97J05`, `a01J04`,
  Mathlib's Taylor-series and meromorphic normal-form/order APIs, and the
  repository lemma index.  The remaining first conjunct is the global step:
  assuming no boundary pole, turn meromorphy plus the compiled localization
  into holomorphy on a uniform disk of radius `r > 1`, identify `a n` with
  the Taylor coefficients using the pointwise `HasSum` family, and contradict
  `hradius_gt` via absolute Taylor convergence.

  For the second conjunct one must additionally prove finiteness of the
  boundary pole set, subtract all simple principal parts, extend the remainder
  holomorphically across the circle, and identify its Taylor coefficients.
  `a97J05` contains the single-pole removable-singularity construction but is
  itself still open at the pointwise-`HasSum` to power-series conversion, so
  it is not a reusable closed dependency.  No unproved intermediate assertion
  was introduced and the frozen theorem statement is unchanged.

  CLOSER HOP 3 goes beyond that boundary via Mathlib's meromorphic divisor.
  `apm_a95J04_boundary_poles_finite` restricts its locally finite support to
  the compact unit sphere, proving the boundary-pole set finite. Searches of
  `CanonicalDecomposition`, `FactorizedRational`, and
  `MeromorphicOn.extract_zeros_poles` found divisor factorization, but no
  additive simple-principal-part decomposition suitable for coefficient
  bounds. The pointwise `HasSum`-to-Taylor conversion and the larger-disk
  absolute-convergence argument remain open; the frozen statement is
  unchanged.
  -/
  sorry
