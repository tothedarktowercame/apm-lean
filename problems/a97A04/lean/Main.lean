import Mathlib

/-!
# APM a97A04 — measurability of the pointwise convergence set

For a sequence of measurable real-valued functions, the set of points where
the numerical sequence converges is measurable.  The source's pointwise
boundedness assumption is retained explicitly, although the standard Cauchy
criterion proof does not need it because `ℝ` is complete.

## Statement repairs

None.

## Encoding questions

None. The neighbourhood filter is written explicitly as `Filter.nhds`.
-/

open Filter

theorem apm_a97a04
    {X : Type*} [MeasurableSpace X]
    (f : ℕ → X → ℝ)
    (hf : ∀ n : ℕ, Measurable (f n))
    (hbounded : ∀ x : X, ∃ C : ℝ, ∀ n : ℕ, |f n x| ≤ C) :
    MeasurableSet {x : X |
      ∃ l : ℝ, Tendsto (fun n : ℕ ↦ f n x) atTop (nhds l)} := by
  sorry
