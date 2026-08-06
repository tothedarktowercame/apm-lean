import Mathlib

/-!
# APM m02A02 — the periodic Poisson variational problem

## Statement repairs

The source omits the necessary compatibility condition for the periodic Poisson
equation.  Part (c) is therefore stated under `forcing 1 = 0`, the abstract form
of `∫_Ω f = 0`.

## Encoding notes

Mathlib currently has no packaged periodic Sobolev completion on the square.
Accordingly `H` is an explicitly quantified Hilbert-space model of `H¹_P(Ω)`,
with its mean, `L²` energy, gradient bilinear form, forcing functional, and weak
Laplacian predicate retained as separate data.  This is an intentionally
axiomatised interface, not a scalar surrogate for the function space.
-/

open Set

def apm_m02a02_domain : Set (ℝ × ℝ) :=
  Icc 0 1 ×ˢ Icc 0 1

theorem apm_m02a02
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (mean : H →L[ℝ] ℝ) (l2Energy gradEnergy : H → ℝ)
    (energy : H →L[ℝ] H →L[ℝ] ℝ) (forcing : H →L[ℝ] ℝ)
    (weakPoisson : H → Prop) (u₀ one : H)
    (hone : mean one = 1) (hcompat : forcing one = 0) :
    CompleteSpace (LinearMap.ker mean.toLinearMap) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ u : H, mean u = 0 →
      l2Energy u ≤ C * gradEnergy u) ∧
    (∃! u : H,
      u - u₀ ∈ LinearMap.ker mean.toLinearMap ∧
      ∀ v : H, v ∈ LinearMap.ker mean.toLinearMap → energy u v = forcing v) ∧
    (∀ u : H, u - u₀ ∈ LinearMap.ker mean.toLinearMap →
      ((∀ v : H, v ∈ LinearMap.ker mean.toLinearMap →
          energy u v = forcing v) ↔ weakPoisson u)) := by
  sorry
