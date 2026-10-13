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

/-- Smooth test functions make the formal-adjoint expression continuous. -/
lemma apm_m93J04_formalAdjoint_continuous (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Continuous (apm_m93J04_formalAdjoint φ) := by
  have hφ₂ : Continuous (iteratedDeriv 2 φ) :=
    hφ.continuous_iteratedDeriv 2 (by norm_cast)
  have hφ₁ : Continuous (deriv φ) := hφ.continuous_deriv (by norm_cast)
  have hφ₀ : Continuous φ := hφ.continuous
  unfold apm_m93J04_formalAdjoint
  fun_prop

/-- On the two sides of the pole, the expanded weak integrand is interval
integrable.  This supplies the hypotheses needed by the adjacent-interval
split and by the eventual integrations by parts. -/
lemma apm_m93J04_branch_intervalIntegrable (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    IntervalIntegrable
        (fun x ↦ apm_m93J04_kernel x y * apm_m93J04_formalAdjoint φ x)
        volume 0 y ∧
      IntervalIntegrable
        (fun x ↦ apm_m93J04_kernel x y * apm_m93J04_formalAdjoint φ x)
        volume y 1 := by
  have hadj := apm_m93J04_formalAdjoint_continuous φ hφ
  constructor
  · apply ContinuousOn.intervalIntegrable
    have hb : Continuous
        (fun x : ℝ ↦ (x * Real.log y / y ^ 2) * apm_m93J04_formalAdjoint φ x) := by
      fun_prop
    apply hb.continuousOn.congr
    intro x hx
    have hxy : x ≤ y := by
      rw [uIcc_of_le hy.1.le] at hx
      exact hx.2
    simp only
    rw [apm_m93J04_kernel_of_le hxy]
  · apply ContinuousOn.intervalIntegrable
    have hb : Continuous
        (fun x : ℝ ↦ (x * Real.log x / y ^ 2) * apm_m93J04_formalAdjoint φ x) := by
      exact (Real.continuous_mul_log.div_const _).mul hadj
    apply hb.continuousOn.congr
    intro x hx
    have hyx : y ≤ x := by
      rw [uIcc_of_le hy.2.le] at hx
      exact hx.1
    by_cases hxy : x = y
    · subst x
      simp only
      rw [apm_m93J04_kernel_of_le le_rfl]
    · simp only
      rw [apm_m93J04_kernel_of_lt (lt_of_le_of_ne hyx (Ne.symm hxy))]

private def apm_m93J04_leftPrimitive (y : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log y / y ^ 2 * (x ^ 3 * deriv φ x + 2 * x ^ 2 * φ x)

private def apm_m93J04_rightPrimitive (y : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (x ^ 3 * Real.log x * deriv φ x + x ^ 2 * (2 * Real.log x - 1) * φ x) /
    y ^ 2

/-- The left weighted formal adjoint has an explicit primitive.  This replaces
two integrations by parts by one application of the interval FTC. -/
lemma apm_m93J04_left_branch_integral (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    (∫ x in (0 : ℝ)..y,
        (x * Real.log y / y ^ 2) * apm_m93J04_formalAdjoint φ x) =
      apm_m93J04_leftPrimitive y φ y - apm_m93J04_leftPrimitive y φ 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := apm_m93J04_leftPrimitive y φ)
  · intro x hx
    have h0 : HasDerivAt φ (deriv φ x) x :=
      (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
    have h1 : HasDerivAt (deriv φ) (deriv (deriv φ) x) x := by
      simpa [iteratedDeriv_one] using
        ((hφ.differentiable_iteratedDeriv 1 (by simp)).differentiableAt.hasDerivAt)
    unfold apm_m93J04_leftPrimitive
    rw [apm_m93J04_formalAdjoint_eq]
    convert (((((hasDerivAt_id x).pow 3).mul h1).add
      (((hasDerivAt_const x (2 : ℝ)).mul ((hasDerivAt_id x).pow 2)).mul h0)).const_mul
        (Real.log y / y ^ 2)) using 1 <;> simp [id] <;> ring
  · exact (Continuous.intervalIntegrable
      ((continuous_id.mul continuous_const).div_const _ |>.mul
        (apm_m93J04_formalAdjoint_continuous φ hφ))) 0 y

/-- The right weighted formal adjoint has an explicit primitive away from
zero.  Positivity of the pole makes the logarithmic derivative legitimate. -/
lemma apm_m93J04_right_branch_integral (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    (∫ x in y..(1 : ℝ),
        (x * Real.log x / y ^ 2) * apm_m93J04_formalAdjoint φ x) =
      apm_m93J04_rightPrimitive y φ 1 - apm_m93J04_rightPrimitive y φ y := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := apm_m93J04_rightPrimitive y φ)
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hy.1 (by
      rw [uIcc_of_le hy.2.le] at hx
      exact hx.1)
    have h0 : HasDerivAt φ (deriv φ x) x :=
      (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
    have h1 : HasDerivAt (deriv φ) (deriv (deriv φ) x) x := by
      simpa [iteratedDeriv_one] using
        ((hφ.differentiable_iteratedDeriv 1 (by simp)).differentiableAt.hasDerivAt)
    unfold apm_m93J04_rightPrimitive
    rw [apm_m93J04_formalAdjoint_eq]
    convert ((((((hasDerivAt_id x).pow 3).mul (Real.hasDerivAt_log hxpos.ne')).mul h1).add
      (((((hasDerivAt_id x).pow 2).mul
        (((Real.hasDerivAt_log hxpos.ne').const_mul 2).sub_const 1))).mul h0)).div_const
          (y ^ 2)) using 1 <;> simp [id] <;> field_simp [hxpos.ne'] <;> ring
  · exact (Continuous.intervalIntegrable
      ((Real.continuous_mul_log.div_const _).mul
        (apm_m93J04_formalAdjoint_continuous φ hφ))) y 1

theorem apm_m93j04 :
    ∀ y : ℝ, y ∈ Ioo (0 : ℝ) 1 →
      ∀ φ : ℝ → ℝ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
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

  Closer hop 3 compiles the remaining integrability layer:
  `apm_m93J04_formalAdjoint_continuous` derives continuity from `ContDiff`,
  and `apm_m93J04_branch_intervalIntegrable` uses the two kernel normal forms,
  `Real.continuous_mul_log`, and positivity of `y` to prove interval
  integrability on both `[0,y]` and `[y,1]`.  A final inspection of Mathlib's
  integration-by-parts variants found no lemma performing the necessary
  second-order weighted calculation in one step.  The four applications and
  their boundary-term algebra therefore remain open without an unproved
  assertion.
  -/
  intro y hy φ hφ _ hsupp
  obtain ⟨hφ0, hdφ0, hφ1, hdφ1⟩ :=
    apm_m93J04_testFunction_endpoints φ hsupp
  obtain ⟨hint0, hint1⟩ :=
    apm_m93J04_branch_intervalIntegrable y hy φ hφ
  rw [apm_m93J04_integral_Ioo_split _ hint0 hint1]
  have hleft :
      (∫ x in (0 : ℝ)..y,
          apm_m93J04_kernel x y * apm_m93J04_formalAdjoint φ x) =
        ∫ x in (0 : ℝ)..y,
          (x * Real.log y / y ^ 2) * apm_m93J04_formalAdjoint φ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [apm_m93J04_kernel_of_le]
    rw [uIcc_of_le hy.1.le] at hx
    exact hx.2
  have hright :
      (∫ x in y..(1 : ℝ),
          apm_m93J04_kernel x y * apm_m93J04_formalAdjoint φ x) =
        ∫ x in y..(1 : ℝ),
          (x * Real.log x / y ^ 2) * apm_m93J04_formalAdjoint φ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le hy.2.le] at hx
    rcases eq_or_lt_of_le hx.1 with rfl | hyx
    · rw [apm_m93J04_kernel_of_le le_rfl]
    · rw [apm_m93J04_kernel_of_lt hyx]
  rw [hleft, hright, apm_m93J04_left_branch_integral y hy φ hφ,
    apm_m93J04_right_branch_integral y hy φ hφ]
  unfold apm_m93J04_leftPrimitive apm_m93J04_rightPrimitive
  rw [hφ0, hdφ0, hφ1, hdφ1]
  field_simp [hy.1.ne']
  ring
