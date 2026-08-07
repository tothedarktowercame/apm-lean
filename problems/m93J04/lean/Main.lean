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

lemma apm_m93J04_kernel_of_le {x y : ℝ} (hxy : x ≤ y) :
    apm_m93J04_kernel x y = x * Real.log y / y ^ 2 := by
  simp [apm_m93J04_kernel, hxy]

lemma apm_m93J04_kernel_of_lt {x y : ℝ} (hyx : y < x) :
    apm_m93J04_kernel x y = x * Real.log x / y ^ 2 := by
  simp [apm_m93J04_kernel, not_le_of_gt hyx]

/-- The algebraic jump of the two branch derivatives at the pole.  This is
the coefficient left after the two integrations by parts. -/
lemma apm_m93J04_kernel_derivative_jump (y : ℝ) :
    (Real.log y + 1) / y ^ 2 - Real.log y / y ^ 2 = 1 / y ^ 2 := by
  ring

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

  Closer hop 1 proves the exact branch normal forms
  `apm_m93J04_kernel_of_le` and `apm_m93J04_kernel_of_lt`, and isolates the
  inner boundary coefficient as `apm_m93J04_kernel_derivative_jump`. Mathlib's
  `Real.hasDerivAt_mul_log` and `Real.deriv2_mul_log` supply the needed branch
  derivatives. Solved artifact `a02J03` demonstrates deriving endpoint
  vanishing from `support φ ⊆ Ioo a b` and then invoking
  `integral_mul_deriv_eq_deriv_mul`; `ConstructionTargets.Sinc` gives another
  compiled integration-by-parts example.

  Neither example packages the remaining second-order calculation. The live
  bridge is now the set-integral-to-two-interval-integrals conversion, the
  corresponding integrability proofs, and four applications of integration
  by parts whose outer terms vanish and whose inner terms use the proved jump.
  The frozen statement was left unchanged.
  -/
  sorry
