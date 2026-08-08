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

/-- Test functions whose support lies in `(0,1)`
vanish together with their first derivative at both outer endpoints. -/
lemma apm_m93J04_testFunction_endpoints
    (φ : ℝ → ℝ)
    (hsupp : Function.support φ ⊆ Ioo (0 : ℝ) 1) :
    φ 0 = 0 ∧ deriv φ 0 = 0 ∧ φ 1 = 0 ∧ deriv φ 1 = 0 := by
  have hzero_left : ∀ x ≤ (0 : ℝ), φ x = 0 := by
    intro x hx
    by_contra hne
    exact (not_lt_of_ge hx) (hsupp hne).1
  have hzero_right : ∀ x, (1 : ℝ) ≤ x → φ x = 0 := by
    intro x hx
    by_contra hne
    exact (not_lt_of_ge hx) (hsupp hne).2
  have hφ0 : φ 0 = 0 := hzero_left 0 le_rfl
  have hφ1 : φ 1 = 0 := hzero_right 1 le_rfl
  refine ⟨hφ0, ?_, hφ1, ?_⟩
  · refine HasDerivWithinAt.deriv_eq_zero ?_
      (uniqueDiffOn_Iic 0 0 (mem_Iic.mpr le_rfl))
    refine (hasDerivWithinAt_const 0 (Iic 0) 0).congr_of_mem ?_ (mem_Iic.mpr le_rfl)
    intro x hx
    exact hzero_left x hx
  · refine HasDerivWithinAt.deriv_eq_zero ?_
      (uniqueDiffOn_Ici 1 1 (mem_Ici.mpr le_rfl))
    refine (hasDerivWithinAt_const 1 (Ici 1) 0).congr_of_mem ?_ (mem_Ici.mpr le_rfl)
    intro x hx
    exact hzero_right x hx

/-- Convert the puncture-free set integral to the two adjacent interval
integrals used by the branchwise calculation. -/
lemma apm_m93J04_integral_Ioo_split
    (f : ℝ → ℝ) {y : ℝ}
    (hleft : IntervalIntegrable f volume 0 y)
    (hright : IntervalIntegrable f volume y 1) :
    (∫ x in Ioo (0 : ℝ) 1, f x) =
      (∫ x in (0 : ℝ)..y, f x) + ∫ x in y..1, f x := by
  rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

def apm_m93J04_formalAdjoint (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  x ^ 2 * iteratedDeriv 2 φ x + 5 * x * deriv φ x + 4 * φ x

lemma apm_m93J04_formalAdjoint_eq (φ : ℝ → ℝ) (x : ℝ) :
    apm_m93J04_formalAdjoint φ x =
      x ^ 2 * deriv (deriv φ) x + 5 * x * deriv φ x + 4 * φ x := by
  unfold apm_m93J04_formalAdjoint
  have h : iteratedDeriv 2 φ = deriv (deriv φ) := by
    calc
      iteratedDeriv 2 φ = iteratedDeriv (1 + 1) φ := by norm_num
      _ = deriv (iteratedDeriv 1 φ) := iteratedDeriv_succ
      _ = deriv (deriv φ) := by rw [iteratedDeriv_one]
  rw [h]

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

  Closer hop 2 closes two of those bookkeeping layers instead of repeating
  the API search. `apm_m93J04_testFunction_endpoints` derives both value and
  first-derivative vanishing at `0` and `1` directly from support containment,
  using one-sided unique differentiability at the endpoints.
  `apm_m93J04_integral_Ioo_split` converts the set integral into the two
  adjacent interval integrals once their interval integrability is known, and
  `apm_m93J04_formalAdjoint_eq` rewrites `iteratedDeriv 2` to the nested
  derivative required by integration by parts.

  Renewed consultation of `LEMMA-INDEX.md`, `ConstructionTargets.Sinc`,
  solved artifact `a02J03`, Mathlib's set-integral and repeated-derivative
  sources, and git history found no second-order branch lemma. The remaining
  bridge is narrower: establish interval integrability of the fully expanded
  products on `[0,y]` and `[y,1]`, then perform the four integration-by-parts
  applications and combine their inner boundary terms via the compiled jump.
  The frozen statement is unchanged.
  -/
  sorry
