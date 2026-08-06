import Mathlib

/-!
# APM m95J05: A first-order fundamental solution

## Statement repairs

None.

## Encoding questions

None. The general definition uses Mathlib's genuine space of distributions.
For `d/dt + λ`, the distributional equation is stated in its exact weak form
against test functions, and the inhomogeneous solution is the actual causal
convolution integral.  The main theorem asserts that the displayed kernel
satisfies that weak equation; it does not restate the definition of
`apm_m95J05_isFundamentalSolution` as an equivalence.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions

noncomputable section

def apm_m95J05_realDomain : Opens ℝ := ⊤

def apm_m95J05_isFundamentalSolution
    (A : 𝓓'(apm_m95J05_realDomain, ℝ) → 𝓓'(apm_m95J05_realDomain, ℝ))
    (dirac T : 𝓓'(apm_m95J05_realDomain, ℝ)) : Prop :=
  A T = dirac

def apm_m95J05_isTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ

def apm_m95J05_fundamental (lam t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-lam * t) else 0

/-- A locally integrable kernel is a fundamental solution of `d/dt + λ` when
its distributional pairing with the formal adjoint sends every test function
to evaluation at zero. -/
def apm_m95J05_isFundamentalKernel (lam : ℝ) (E : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, apm_m95J05_isTestFunction ψ →
    (∫ t, E t * (-deriv ψ t + lam * ψ t)) = ψ 0

def apm_m95J05_solution (lam : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Iic t, Real.exp (-lam * (t - s)) * φ s

theorem apm_m95j05 :
    (∀ lam : ℝ,
      apm_m95J05_isFundamentalKernel lam (apm_m95J05_fundamental lam)) ∧
    (∀ (lam : ℝ) (φ : ℝ → ℝ),
      apm_m95J05_isTestFunction φ →
        ContDiff ℝ ⊤ (apm_m95J05_solution lam φ) ∧
        ∀ t : ℝ,
          deriv (apm_m95J05_solution lam φ) t +
            lam * apm_m95J05_solution lam φ t = φ t) := by
  sorry
