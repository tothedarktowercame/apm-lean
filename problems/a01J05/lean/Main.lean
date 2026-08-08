import Mathlib

/-!
# APM a01J05 — critical points of a finite Blaschke product

## Statement repairs

The hypothesis `0 < N` is made explicit.  Without it the source permits the
constant function `f = 1`: it has no zeros, while its derivative vanishes
identically, so the claimed `N - 1` zero count is false.

Zeros are counted with multiplicity using Mathlib's `analyticOrderAt`, rather
than by the cardinality of a set of distinct zeros.
-/

open Complex Metric Set
open scoped ENNReal

noncomputable section

def apm_a01J05_disk : Set ℂ :=
  ball 0 1

def apm_a01J05_circle : Set ℂ :=
  sphere 0 1

/-- Total order of vanishing over the open unit disk. -/
def apm_a01J05_zeroMultiplicity (f : ℂ → ℂ) : ℕ∞ :=
  by
    classical
    exact ∑' z : ℂ, if z ∈ apm_a01J05_disk then analyticOrderAt f z else 0

/-- Analyticity on a slightly larger closed disk gives analyticity at every
point of the unit disk. -/
lemma apm_a01J05_analyticAt_of_closedBall
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) : AnalyticAt ℂ f z := by
  have hr : (1 : ℝ) < 1 + ε := by linarith
  have hz' : z ∈ ball (0 : ℂ) (1 + ε) := by
    exact (ball_subset_ball hr.le) hz
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hf.mono ball_subset_closedBall
  exact hdiff.analyticAt (isOpen_ball.mem_nhds hz')

/-- The derivative is analytic throughout the unit disk under the same
neighborhood hypothesis. -/
lemma apm_a01J05_deriv_analyticAt_of_closedBall
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) : AnalyticAt ℂ (deriv f) z := by
  have hr : (1 : ℝ) < 1 + ε := by linarith
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hf.mono ball_subset_closedBall
  have han : AnalyticOnNhd ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hdiff.analyticOnNhd isOpen_ball
  exact han.deriv z ((ball_subset_ball hr.le) hz)

/-- Pointwise multiplicity drop under differentiation.  Summing this identity
is one local ingredient of the global critical-point count. -/
lemma apm_a01J05_order_deriv_add_one
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) :
    analyticOrderAt (deriv f) z + 1 =
      analyticOrderAt (fun w => f w - f z) z := by
  exact (apm_a01J05_analyticAt_of_closedBall hε hf hz).analyticOrderAt_deriv_add_one

theorem apm_a01j05 (f : ℂ → ℂ) (N : ℕ)
    (hN : 0 < N)
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    apm_a01J05_zeroMultiplicity (deriv f) = (N - 1 : ℕ) := by
  /-
  Closer hop 2 compiles the local analytic layer above.  The neighborhood
  hypothesis gives `AnalyticAt` for both `f` and `deriv f` at every point of
  the unit disk, and `apm_a01J05_order_deriv_add_one` records Mathlib's exact
  pointwise multiplicity-drop identity.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
  `CanonicalDecomposition`, divisor, argument-principle, and Gauss--Lucas
  sources, related artifacts `a94A09` and `a94A10`, and git history found no
  theorem turning constant boundary norm into a finite Blaschke-product
  factorization, nor a theorem counting the critical points of such a product.
  `ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum` counts
  zeros of one analytic function, but it does not provide the required global
  relation between the divisor sums of `f` and `deriv f`.

  Closure still requires constructing the finite Blaschke factorization from
  `hf_boundary` and `hf_zeros` (including finiteness/attainment for the custom
  `tsum`), then proving the classical `N - 1` interior critical-point count,
  e.g. by reflection and the rational-map critical divisor or by an argument-
  principle calculation for the logarithmic derivative.
  -/
  sorry
