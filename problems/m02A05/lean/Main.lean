import Mathlib

/-!
# APM m02A05 — a coupled variational problem

## Statement repairs

None.
-/

open Set MeasureTheory

def apm_m02a05_admissible (x y : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 x ∧ ContDiff ℝ 2 y ∧
  x 0 = 0 ∧ y 0 = 0 ∧ x (Real.pi / 2) = 1 ∧ y (Real.pi / 2) = 1

noncomputable def apm_m02a05_J (x y : ℝ → ℝ) : ℝ :=
  ∫ t in Icc 0 (Real.pi / 2),
    (deriv x t) ^ 2 + (deriv y t) ^ 2 + 2 * x t * y t

noncomputable def apm_m02a05_extremal (t : ℝ) : ℝ :=
  Real.sinh t / Real.sinh (Real.pi / 2)

theorem apm_m02a05 :
    (∀ x y : ℝ → ℝ, apm_m02a05_admissible x y →
      ((∀ t ∈ Ioo 0 (Real.pi / 2),
          deriv (deriv x) t = y t ∧ deriv (deriv y) t = x t) ↔
        x = apm_m02a05_extremal ∧ y = apm_m02a05_extremal)) ∧
    (∀ x y : ℝ → ℝ, apm_m02a05_admissible x y →
      apm_m02a05_J apm_m02a05_extremal apm_m02a05_extremal ≤
        apm_m02a05_J x y) ∧
    (∀ B : ℝ, ∃ x y : ℝ → ℝ,
      apm_m02a05_admissible x y ∧ B < apm_m02a05_J x y) := by
  /-
  SKIPPED (frozen-statement defect). The first conjunct concludes the global
  function equalities `x = apm_m02a05_extremal` and
  `y = apm_m02a05_extremal`, but all boundary conditions, ODE hypotheses, and
  the functional constrain the functions only on `[0, π/2]`.

  Concretely, start with the displayed extremal and add to `x` any nonzero
  smooth bump supported in `(π, π + 1)`, leaving `y` unchanged. The modified
  pair is globally `ContDiff`, has the same endpoint values, and agrees with
  the extremal on a neighborhood of `[0, π/2]`; hence it satisfies
  `x'' = y` and `y'' = x` throughout the required `Ioo`, but `x` is not
  globally equal to `apm_m02a05_extremal`. Thus the forward implication in
  the asserted equivalence is false.

  The intended conclusion must use `Set.EqOn` on `Icc 0 (π/2)` (or quantify
  functions on the interval subtype). The statement is frozen, so no repair
  was made.
  -/
  sorry
