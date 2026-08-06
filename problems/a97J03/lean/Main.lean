import Mathlib

/-!
# APM a97J03: Convolution of conjugate Lp functions

## Statement repairs

None.

## Encoding questions

None. Because the source explicitly declares `h : ℝ → ℂ`, the `L^p` and
`L^q` functions are encoded as complex-valued measurable functions. Membership
is represented by Mathlib's `MemLp` at the finite real exponents embedded in
`ℝ≥0∞`.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

/-- The convolution `h(y) = ∫ x, f(y-x)g(x) dx`. -/
def apm_a97J03_convolution (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, f (y - x) * g x ∂volume

theorem apm_a97j03
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1)
    (f g : ℝ → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Continuous (apm_a97J03_convolution f g) ∧
      Tendsto (apm_a97J03_convolution f g) atTop (𝓝 0) ∧
      Tendsto (apm_a97J03_convolution f g) atBot (𝓝 0) := by
  sorry
