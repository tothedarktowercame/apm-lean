import Mathlib

/-!
# APM m93J03: A nonlinear integral equation near its trivial branch

## Statement repairs

The printed global uniqueness claim is stronger than, and is not established
by, the intended implicit-function argument. The exact finite-dimensional
reduction has additional nonzero branches already at `ε = 0`; the invertible
Jacobian proves uniqueness only in a neighborhood of the trivial solution.
We therefore state the minimally repaired local result: fixed radii `δ,η > 0`
give a unique solution with `|ε| < δ` and uniform size below `η`.

## Encoding questions

None. The equation uses the Lebesgue integral on `[-π,π]`; continuity and
uniqueness are both restricted to that exact interval.
-/

open MeasureTheory Set

noncomputable section

def apm_m93J03_isSolution (ε : ℝ) (x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc (-Real.pi) Real.pi) ∧
  ∀ t ∈ Icc (-Real.pi) Real.pi,
    x t = ε + ∫ s in Icc (-Real.pi) Real.pi, Real.sin (t + s + x s)

def apm_m93J03_isSmall (x : ℝ → ℝ) (η : ℝ) : Prop :=
  ∀ t ∈ Icc (-Real.pi) Real.pi, |x t| < η

theorem apm_m93j03 :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧
      ∀ ε : ℝ, |ε| < δ →
        ∃ x : ℝ → ℝ,
          apm_m93J03_isSolution ε x ∧
          apm_m93J03_isSmall x η ∧
          ∀ y : ℝ → ℝ,
            apm_m93J03_isSolution ε y →
            apm_m93J03_isSmall y η →
            EqOn x y (Icc (-Real.pi) Real.pi) := by
  sorry
