import Mathlib

/-!
# APM m93J04: A fundamental solution for an Euler operator

## Statement repairs

None. The duplicated word "Let" in the source is editorial and does not alter
the mathematical statement.

## Encoding questions

None. The distributional identity is stated in its exact weak form against
smooth compactly supported test functions on `(0,1)`. The expression in the
integral is the formal adjoint of `x^2 ∂_x^2 - x ∂_x + 1` applied to the test
function.
-/

open MeasureTheory Set

noncomputable section

def apm_m93J04_kernel (x y : ℝ) : ℝ :=
  if x ≤ y then x * Real.log y / y ^ 2 else x * Real.log x / y ^ 2

def apm_m93J04_formalAdjoint (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  x ^ 2 * iteratedDeriv 2 φ x + 5 * x * deriv φ x + 4 * φ x

theorem apm_m93j04 :
    ∀ y : ℝ, y ∈ Ioo (0 : ℝ) 1 →
      ∀ φ : ℝ → ℝ,
        ContDiff ℝ ⊤ φ →
        HasCompactSupport φ →
        Function.support φ ⊆ Ioo (0 : ℝ) 1 →
        (∫ x in Ioo (0 : ℝ) 1,
            apm_m93J04_kernel x y * apm_m93J04_formalAdjoint φ x) = φ y := by
  /-
  Boundary: a direct proof must convert the set integral over `Ioo 0 1`
  into interval integrals split at `y`, unfold the two branches of the
  kernel, and integrate by parts twice on each side. It then has to derive
  vanishing values and derivatives at `0` and `1` from
  `support φ ⊆ Ioo 0 1`, discharge interval-integrability obligations for
  `x`, `x * log x`, and the derivatives of `φ`, and simplify the two inner
  boundary terms to the derivative jump `1 / y ^ 2`, yielding `φ y`.

  I searched the interval-integral APIs
  `intervalIntegral.integral_mul_deriv_eq_deriv_mul`,
  `intervalIntegral.integral_deriv_mul_eq_sub`, and
  `intervalIntegral.integral_eq_sub_of_hasDerivAt`. They support the
  classical calculation, but I did not complete the set-integral splitting,
  support-to-boundary lemmas, and repeated integration-by-parts bookkeeping
  needed for this exact weak identity within this pass.
  -/
  sorry
