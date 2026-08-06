import Mathlib

/-!
# APM m02A06

## Statement repairs

The source claims uniqueness for every `ε > 0`, but the contraction argument only
gives uniqueness in a bounded ball when `ε` is sufficiently small.  This is
load-bearing: already for `f = 0`, the first integral of the ODE rules out a
decaying solution with `u(0) = 1` when `ε > 3/2`.  The statement below makes
the contraction regime and its uniqueness ball explicit, using a supplied
uniform bound `C` for `f`.

## Encoding notes

The solution is a genuine twice continuously differentiable function on the
closed half-line, and `u(∞) = 0` is encoded as convergence along `atTop`.
-/

open Filter Set
open scoped ContDiff Topology

def apm_m02a06_IsSolution (ε : ℝ) (f u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Ici 0) ∧
  (∀ x ∈ Ioi (0 : ℝ), -deriv (deriv u) x + u x - ε * (u x) ^ 2 = f x) ∧
  u 0 = 1 ∧ Tendsto u atTop (nhds 0)

theorem apm_m02a06
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hf_support : Function.support f ⊆ Ioi 0)
    (C : ℝ) (hC : 0 ≤ C) (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * (1 + C))) :
    ∃! u : ℝ → ℝ,
      apm_m02a06_IsSolution ε f u ∧
      ∀ x ∈ Ici (0 : ℝ), |u x| ≤ 2 * (1 + C) := by
  sorry
