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

theorem apm_a01j05 (f : ℂ → ℂ) (N : ℕ)
    (hN : 0 < N)
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    apm_a01J05_zeroMultiplicity (deriv f) = (N - 1 : ℕ) := by
  sorry
