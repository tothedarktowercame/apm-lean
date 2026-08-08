import Mathlib

/-!
# APM m94J05 — a small nonlinear Euler boundary-value problem

## Statement repairs

The source's unrestricted uniqueness claim is false: even at zero forcing the
associated superlinear two-point Dirichlet problem has a nonzero large branch.
The conclusion is therefore stated as existence and uniqueness in a uniform
sup-norm ball, which is exactly the small branch controlled by the hinted
contraction argument.

Solutions are represented by ambient functions `ℝ → ℝ` to use Mathlib's
derivatives.  Consequently uniqueness is stated with `Set.EqOn` on `[1,2]`;
values outside the source interval are intentionally irrelevant.

## Encoding questions

None.
-/

open Set

def IsM94J05Solution (f x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 x (Icc 1 2) ∧
  x 1 = 0 ∧ x 2 = 0 ∧
  ∀ t ∈ Icc (1 : ℝ) 2,
    t ^ 2 * iteratedDeriv 2 x t + 2 * t * deriv x t = f t + (x t) ^ 2

theorem apm_m94j05 :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ f : ℝ → ℝ,
        ContinuousOn f (Icc 1 2) →
        (∀ t ∈ Icc (1 : ℝ) 2, |f t| < ε) →
        ∃ x : ℝ → ℝ,
          IsM94J05Solution f x ∧
          (∀ t ∈ Icc (1 : ℝ) 2, |x t| ≤ r) ∧
          ∀ z : ℝ → ℝ,
            IsM94J05Solution f z →
            (∀ t ∈ Icc (1 : ℝ) 2, |z t| ≤ r) →
            EqOn z x (Icc 1 2) := by
  sorry
