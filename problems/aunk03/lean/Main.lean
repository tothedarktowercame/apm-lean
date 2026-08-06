import Mathlib

/-!
# APM aunk03 — the quartic reciprocal sum

## Statement repairs

None.

## Encoding notes

The meromorphic function and the half-integer square contour prescribed by the
problem are defined explicitly.  The contour is represented by its boundary
set; its four oriented edges belong to the proof rather than the proposition.
The series is indexed by `k : ℕ` with summand `(k + 1)⁻⁴`, faithfully encoding
the source's sum from `k = 1`.
-/

open Set

noncomputable def apm_aunk03_kernel (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) / z ^ 4

def apm_aunk03_squareContour (n : ℕ) : Set ℂ :=
  let r : ℝ := n + (1 / 2 : ℝ)
  {z | (|z.re| = r ∧ |z.im| ≤ r) ∨ (|z.im| = r ∧ |z.re| ≤ r)}

theorem apm_aunk03 :
    (∑' k : ℕ, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 4) = Real.pi ^ 4 / 90 := by
  sorry
