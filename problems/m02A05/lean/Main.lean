import Mathlib

/-!
# APM m02A05 — a coupled variational problem

## Statement repairs

2026 repair (guide, attempt 1, obligation
d6fd972b4c8b2dd896da1fde27e5ddb5536d78914a38729d0de77935beacb6e6,
frame f203): the first conjunct originally concluded the global function
equalities `x = apm_m02a05_extremal` and `y = apm_m02a05_extremal`, which is
refuted by adding a smooth bump supported outside `[0, π/2]`. The conclusion
is now `Set.EqOn` on `Icc 0 (π/2)`, the interval on which the boundary
conditions, the ODE, and the functional constrain the pair. The second and
third conjuncts are unchanged. No logical problem-id change.
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
        (Set.EqOn x apm_m02a05_extremal (Icc 0 (Real.pi / 2)) ∧
         Set.EqOn y apm_m02a05_extremal (Icc 0 (Real.pi / 2))))) ∧
    (∀ x y : ℝ → ℝ, apm_m02a05_admissible x y →
      apm_m02a05_J apm_m02a05_extremal apm_m02a05_extremal ≤
        apm_m02a05_J x y) ∧
    (∀ B : ℝ, ∃ x y : ℝ → ℝ,
      apm_m02a05_admissible x y ∧ B < apm_m02a05_J x y) := by
  /-
  Repaired statement; proof deferred to the solver. The original defect: the
  forward implication required global equality `x = apm_m02a05_extremal`, but
  all hypotheses constrain the pair only on `[0, π/2]`; adding a nonzero
  smooth bump to `x` supported in `(π, π + 1)` refuted it. The repaired
  conclusion is `Set.EqOn` on `Icc 0 (π/2)`.
  -/
  sorry
