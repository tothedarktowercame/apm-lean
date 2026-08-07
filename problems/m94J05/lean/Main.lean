import Mathlib

/-! # APM m94J05: a small nonlinear Euler boundary-value problem

## Statement repairs

None.
-/

open Set

def IsM94J05Solution (f x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 x (Icc 1 2) ∧
  x 1 = 0 ∧ x 2 = 0 ∧
  ∀ t ∈ Icc (1 : ℝ) 2,
    t ^ 2 * iteratedDeriv 2 x t + 2 * t * deriv x t = f t + (x t) ^ 2

theorem apm_m94j05 :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc 1 2) →
      (∀ t ∈ Icc (1 : ℝ) 2, |f t| < ε) →
      ∃! x : ℝ → ℝ, IsM94J05Solution f x := by
  /-
  SKIPPED (statement-strength boundary).  The supplied contraction argument
  constructs a fixed point only in a small closed sup-norm ball and proves
  uniqueness only in that ball.  The frozen conclusion, however, quantifies
  `∃!` over every globally defined function satisfying the BVP, with no
  smallness condition on `x`.  Thus the last step of the informal solution
  does not prove the stated theorem; its own final remark explicitly changes
  the conclusion to uniqueness among small solutions.

  Corpus research found the abstract Banach API
  `ContractingWith.fixedPoint` / `ContractingWith.fixedPoint_unique` and the
  compiled wrapper `contraction_fixedPoint` in sibling `t91A04`, but no
  reusable Green operator for `t^2 x'' + 2 t x'` with Dirichlet boundary
  data.  Siblings `m95J04`, `m94A05`, and `m02A06` stop at the same concrete
  analytic boundary: constructing the integral operator, proving its
  regularity, and establishing uniform estimates.  `LEMMA-INDEX.md`, all
  fully closed artifacts, `ConstructionTargets/`, and `YoungL2.lean` supplied
  no such operator or global uniqueness theorem.  Mathlib's
  `Topology.MetricSpace.Contracting` supplies fixed points on invariant
  complete sets, but cannot upgrade uniqueness in a ball to unrestricted
  uniqueness.

  The frozen statement is likely false as written.  For zero forcing, after
  the substitution `s = 1 / t` and `v(s) = -x(1/s)`, the equation becomes
  `-v'' = v^2 / s^2` on `[1/2,1]` with two zero endpoint values.  The zero
  solution is the small fixed point, while this positive-weight superlinear
  Dirichlet equation has the standard nonzero large branch obtained by
  shooting/variational methods; nothing in the hypotheses excludes it.
  Mathlib's `Analysis.ODE.PicardLindelof` and `Analysis.ODE.Gronwall` provide
  initial-value existence/uniqueness, not the required two-point shooting or
  global uniqueness theorem.  A corrected theorem should include a uniform
  smallness bound on `x` (and express uniqueness within that ball), exactly as
  the contraction proof requires.
  -/
  sorry
