import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# APM a94A04: Orthogonality to all monomials implies zero a.e.

**Problem.** If f : [0,1] -> R is square integrable and satisfies
integral_0^1 x^n f(x) dx = 0 for n = 0,1,2,..., then f = 0 a.e.

## Proof

By linearity, integral p(x) f(x) dx = 0 for every polynomial p.
By Weierstrass, polynomials are dense in C([0,1]), hence dense in L^2.
So f is orthogonal to a dense subspace, forcing ||f||^2 = 0, hence f = 0 a.e.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter Polynomial
open scoped Topology

namespace ApmCanaries.A94A04

/-- Orthogonality extends to all polynomials by linearity. -/
lemma orthogonal_to_polynomials
    {f : ℝ → ℝ} {μ : Measure ℝ}
    (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂μ = 0)
    (p : Polynomial ℝ) :
    ∫ x in Icc (0:ℝ) 1, Polynomial.eval x p * f x ∂μ = 0 := by
  induction p using Polynomial.induction_on' with
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    sorry
  | add p q hp hq =>
    have heval : ∀ x, Polynomial.eval x (p + q) * f x =
        Polynomial.eval x p * f x + Polynomial.eval x q * f x := by
      intro x; rw [Polynomial.eval_add, add_mul]
    rw [show (∫ x in Icc (0:ℝ) 1, Polynomial.eval x (p + q) * f x ∂μ) =
        ∫ x in Icc (0:ℝ) 1, (Polynomial.eval x p * f x + Polynomial.eval x q * f x) ∂μ by
      congr 1 with x; exact heval x]
    sorry

/-- **Main theorem:** f in L^2([0,1]) orthogonal to all monomials is zero a.e.

    **SORRY BOUNDARY:** The proof requires three density arguments:
    (1) Polynomials dense in C([0,1]) via Stone-Weierstrass.
    (2) C([0,1]) dense in L^2([0,1]) via `boundedContinuousFunction_dense`.
    (3) Orthogonality to a dense subspace gives ||f||^2 = 0, hence f = 0 a.e. -/
theorem zero_of_orthogonal_to_monomials
    {f : ℝ → ℝ} {μ : Measure ℝ}
    (hf : MemLp f 2 (μ.restrict (Icc (0:ℝ) 1)))
    (hfm : AEStronglyMeasurable f (μ.restrict (Icc (0:ℝ) 1)))
    (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂μ = 0) :
    f =ᵐ[μ.restrict (Icc (0:ℝ) 1)] 0 := by
  sorry

end ApmCanaries.A94A04
