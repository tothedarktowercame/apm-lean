import Mathlib

/-!
# APM m99A01

## Statement repairs

The source does not specify the admissible function class. The functional is
encoded on `C¹` curves, and extremals are `C²` stationary curves, the standard
minimal regularity needed for the classical Euler--Lagrange formulation.

## Encoding questions

An extremal is encoded intrinsically by vanishing first variation for every
`C¹` endpoint-fixing variation, rather than by taking the Euler--Lagrange ODE
as its definition.
-/

open Set intervalIntegral

/-- The functional in the problem. -/
noncomputable def apm_m99A01_functional (y : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), (deriv y t) ^ 2 + (y t) ^ 2 + 2 * y t

/-- Curves satisfying the stated endpoint constraints. -/
def apm_m99A01_admissible : Set (ℝ → ℝ) :=
  {y | ContDiff ℝ 1 y ∧ y 0 = 0 ∧ y (Real.pi / 2) = 0}

/-- Stationarity under all endpoint-fixing first variations. -/
def apm_m99A01_stationary (y : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η 0 = 0 → η (Real.pi / 2) = 0 →
    HasDerivAt
      (fun s ↦ apm_m99A01_functional (fun t ↦ y t + s * η t)) 0 0

/-- The unique candidate extremal obtained from the boundary-value problem. -/
noncomputable def apm_m99A01_extremal (t : ℝ) : ℝ :=
  Real.cosh t - Real.tanh (Real.pi / 4) * Real.sinh t - 1

/-- The displayed candidate solves the inhomogeneous Euler--Lagrange ODE. -/
lemma apm_m99A01_extremal_ode (t : ℝ) :
    deriv (deriv apm_m99A01_extremal) t - apm_m99A01_extremal t = 1 := by
  have h₁ : deriv apm_m99A01_extremal =
      fun x ↦ Real.sinh x - Real.tanh (Real.pi / 4) * Real.cosh x := by
    funext x
    change deriv (fun z ↦ Real.cosh z - Real.tanh (Real.pi / 4) * Real.sinh z - 1) x = _
    simpa using ((Real.hasDerivAt_cosh x).sub
      ((hasDerivAt_const x (Real.tanh (Real.pi / 4))).mul
        (Real.hasDerivAt_sinh x))).sub_const 1 |>.deriv
  have h₂ : deriv (fun x ↦
      Real.sinh x - Real.tanh (Real.pi / 4) * Real.cosh x) =
      fun x ↦ Real.cosh x - Real.tanh (Real.pi / 4) * Real.sinh x := by
    funext x
    simpa using ((Real.hasDerivAt_sinh x).sub
      ((hasDerivAt_const x (Real.tanh (Real.pi / 4))).mul
        (Real.hasDerivAt_cosh x))) |>.deriv
  rw [h₁, h₂]
  unfold apm_m99A01_extremal
  ring

/-- A concrete endpoint-fixing family used to witness unboundedness above. -/
lemma apm_m99A01_sine_family_admissible (n : ℝ) :
    (fun t : ℝ ↦ n * Real.sin (2 * t)) ∈ apm_m99A01_admissible := by
  refine ⟨by fun_prop, by simp, ?_⟩
  dsimp
  rw [show 2 * (Real.pi / 2) = Real.pi by ring]
  simp

/-- Derivative of the endpoint-fixing family used in the unboundedness
argument. -/
lemma apm_m99A01_deriv_sine_family (n t : ℝ) :
    deriv (fun x : ℝ => n * Real.sin (2 * x)) t =
      2 * n * Real.cos (2 * t) := by
  have h := ((Real.hasDerivAt_sin (2 * t)).comp t
    ((hasDerivAt_id t).const_mul 2)).const_mul n
  convert h.deriv using 1 <;> ring

lemma apm_m99A01_integral_cos_sq_two_mul :
    ∫ t in (0 : ℝ)..(Real.pi / 2), Real.cos (2 * t) ^ 2 = Real.pi / 4 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := fun x : ℝ => Real.cos x ^ 2) (a := (0 : ℝ))
    (b := Real.pi / 2) (c := (2 : ℝ))
  rw [integral_cos_sq] at h
  norm_num [show 2 * (Real.pi / 2) = Real.pi by ring] at h ⊢
  linarith

lemma apm_m99A01_integral_sin_sq_two_mul :
    ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin (2 * t) ^ 2 = Real.pi / 4 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := fun x : ℝ => Real.sin x ^ 2) (a := (0 : ℝ))
    (b := Real.pi / 2) (c := (2 : ℝ))
  rw [integral_sin_sq] at h
  norm_num [show 2 * (Real.pi / 2) = Real.pi by ring] at h ⊢
  linarith

lemma apm_m99A01_integral_sin_two_mul :
    ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin (2 * t) = 1 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := Real.sin) (a := (0 : ℝ)) (b := Real.pi / 2) (c := (2 : ℝ))
  rw [integral_sin] at h
  norm_num [show 2 * (Real.pi / 2) = Real.pi by ring] at h ⊢

/-- Exact value of the functional on the unbounded endpoint-zero family. -/
lemma apm_m99A01_functional_sine_family (n : ℝ) :
    apm_m99A01_functional (fun t : ℝ => n * Real.sin (2 * t)) =
      (5 * Real.pi / 4) * n ^ 2 + 2 * n := by
  unfold apm_m99A01_functional
  simp_rw [apm_m99A01_deriv_sine_family n]
  have hpoint : (fun t : ℝ =>
      (2 * n * Real.cos (2 * t)) ^ 2 + (n * Real.sin (2 * t)) ^ 2 +
        2 * (n * Real.sin (2 * t))) =
      fun t => 4 * n ^ 2 * (Real.cos (2 * t) ^ 2) +
        n ^ 2 * (Real.sin (2 * t) ^ 2) + 2 * n * Real.sin (2 * t) := by
    funext t
    ring
  rw [hpoint]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const_mul]
      rw [apm_m99A01_integral_cos_sq_two_mul,
        apm_m99A01_integral_sin_sq_two_mul,
        apm_m99A01_integral_sin_two_mul]
      ring
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

/-- The functional is unbounded above on the admissible class. -/
lemma apm_m99A01_no_maximum :
    ¬ ∃ y ∈ apm_m99A01_admissible, ∀ z ∈ apm_m99A01_admissible,
      apm_m99A01_functional z ≤ apm_m99A01_functional y := by
  rintro ⟨y, hy, hmax⟩
  let n : ℝ := |apm_m99A01_functional y| + 1
  have hnmem := apm_m99A01_sine_family_admissible n
  have hle := hmax (fun t : ℝ => n * Real.sin (2 * t)) hnmem
  rw [apm_m99A01_functional_sine_family] at hle
  have hquad : 0 ≤ (5 * Real.pi / 4) * n ^ 2 := by positivity
  have habs : apm_m99A01_functional y ≤ |apm_m99A01_functional y| :=
    le_abs_self _
  dsimp [n] at hle hquad
  have htwo : 2 * (|apm_m99A01_functional y| + 1) ≤
      apm_m99A01_functional y := by
    exact le_trans (by linarith only [hquad]) hle
  linarith [abs_nonneg (apm_m99A01_functional y)]

/-- Continuity upgrades the almost-everywhere conclusion of Mathlib's
distributional fundamental lemma to the pointwise statement needed for the
Euler--Lagrange ODE. -/
lemma apm_m99A01_eq_zero_on_Ioo_of_ae
    (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo 0 (Real.pi / 2)))
    (hae : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Ioo 0 (Real.pi / 2) → f x = 0) :
    ∀ x ∈ Ioo 0 (Real.pi / 2), f x = 0 := by
  have hae' : f =ᵐ[MeasureTheory.volume.restrict (Ioo 0 (Real.pi / 2))]
      (0 : ℝ → ℝ) := by
    change ∀ᵐ x ∂MeasureTheory.volume.restrict (Ioo 0 (Real.pi / 2)), f x = 0
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact hae
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hf
    continuous_zero.continuousOn

theorem apm_m99a01 :
    (∀ y : ℝ → ℝ,
      (ContDiff ℝ 2 y ∧ y ∈ apm_m99A01_admissible ∧ apm_m99A01_stationary y) ↔
        y = apm_m99A01_extremal) ∧
    apm_m99A01_extremal ∈ apm_m99A01_admissible ∧
    (∀ y ∈ apm_m99A01_admissible,
      apm_m99A01_functional apm_m99A01_extremal ≤ apm_m99A01_functional y) ∧
    ¬ ∃ y ∈ apm_m99A01_admissible, ∀ z ∈ apm_m99A01_admissible,
      apm_m99A01_functional z ≤ apm_m99A01_functional y := by
  constructor
  · /-
    Boundary: identifying every stationary curve requires differentiating the
    interval integral in the variation parameter, integration by parts, the
    fundamental lemma of the calculus of variations, and uniqueness for the
    resulting inhomogeneous ODE `y'' - y = 1`. I searched Mathlib's
    `HasDerivAt`-under-integral, interval integration-by-parts, and ODE APIs;
    I did not complete this bridge for the frozen stationarity predicate. The
    candidate side of the ODE is proved above as `apm_m99A01_extremal_ode`.

    Closer hop 2 inspected
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le` and the full
    `intervalIntegral.integral_mul_deriv_eq_deriv_mul` family.  Those APIs can
    supply differentiation under the integral and integration by parts after
    their regularity side conditions are assembled.  The newly closed
    `m98J04` arc-length half does not help: its remaining first-variation
    conjunct stops at the same missing fundamental lemma.  Closed artifact
    `a01A03` uses a distributional fundamental lemma only in prose, not as a
    reusable declaration.  Thus the precise live bridge is still converting
    vanishing against all endpoint-zero global `C¹` tests into the pointwise
    ODE, followed by uniqueness of that two-point boundary-value problem.

    Closer hop 3 corrects the earlier resource conclusion: Mathlib does provide
    the distributional fundamental lemma as
    `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.  The new compiled helper
    `apm_m99A01_eq_zero_on_Ioo_of_ae` upgrades its almost-everywhere conclusion
    to pointwise vanishing of a continuous residual using
    `Measure.eqOn_open_of_ae_eq`.  The remaining first-conjunct bridge is now
    upstream: derive the integral residual from the frozen first variation,
    convert interval integrals to whole-space compactly-supported tests, and
    prove uniqueness for `y'' - y = 1` with the two boundary values.
    -/
    sorry
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · unfold apm_m99A01_extremal
      fun_prop
    · simp [apm_m99A01_extremal]
    · unfold apm_m99A01_extremal
      have hc : Real.cosh (Real.pi / 4) ≠ 0 :=
        ne_of_gt (Real.cosh_pos (Real.pi / 4))
      rw [show Real.pi / 2 = 2 * (Real.pi / 4) by ring,
        Real.cosh_two_mul, Real.sinh_two_mul,
        Real.tanh_eq_sinh_div_cosh]
      field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi / 4)]
  · /-
    Closer hop 2 closes nonexistence of a maximum below.  The three scaled
    trigonometric integrals are compiled above using
    `intervalIntegral.mul_integral_comp_mul_left`, `integral_sin`,
    `integral_sin_sq`, and `integral_cos_sq`; they give the exact identity
    `J (n sin(2t)) = (5π/4)n² + 2n`.  `apm_m99A01_no_maximum` then proves
    unboundedness directly.

    The remaining boundary in this conjunct is only global minimality.  It
    requires expanding `J(y₀+h)-J(y₀)`, applying interval integration by parts
    to cancel the cross term using `apm_m99A01_extremal_ode` and the endpoint
    conditions, and retaining the nonnegative integral of `h'²+h²`.  Mathlib's
    integration-by-parts theorem is available, but assembling it with raw
    `deriv` after setting `h = y-y₀` was not completed in this hop.
    -/
    constructor
    · sorry
    · exact apm_m99A01_no_maximum
