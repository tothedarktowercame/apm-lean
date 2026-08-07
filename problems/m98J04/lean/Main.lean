import Mathlib

/-!
# APM m98J04

## Statement repairs

The source does not state regularity assumptions. The Euler--Lagrange part is
minimally stated for a `C²` Lagrangian and a `C²` stationary curve, while the
arc-length minimization ranges over `C¹` graph curves. The two endpoints are
assumed to have distinct horizontal coordinates, ordered as `a < b`, as is
required by the graph parametrization used in the question.

## Encoding questions

Stationarity means vanishing first variation against every `C¹` variation
which fixes both endpoints. Partial derivatives of the Lagrangian are encoded
as ordinary derivatives with the other two arguments held fixed.
-/

open Set intervalIntegral

/-- The variational functional associated to a first-order Lagrangian. -/
noncomputable def apm_m98J04_functional
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, F x (y x) (deriv y x)

/-- Vanishing first variation under endpoint-fixing variations. -/
def apm_m98J04_stationary
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
    HasDerivAt
      (fun t ↦ apm_m98J04_functional F a b (fun x ↦ y x + t * η x)) 0 0

/-- The pointwise Euler--Lagrange equation along a curve. -/
def apm_m98J04_eulerLagrange
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ioo a b,
    HasDerivAt
      (fun t ↦ deriv (fun p ↦ F t (y t) p) (deriv y t))
      (deriv (fun q ↦ F x q (deriv y x)) (y x)) x

/-- Length of a plane curve presented as a graph. -/
noncomputable def apm_m98J04_arcLength (a b : ℝ) (y : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, Real.sqrt (1 + (deriv y x) ^ 2)

/-- The line graph joining `(a, α)` and `(b, β)`. -/
noncomputable def apm_m98J04_line (a b α β : ℝ) (x : ℝ) : ℝ :=
  α + ((β - α) / (b - a)) * (x - a)

/-- `C¹` graph curves with the prescribed endpoints. -/
def apm_m98J04_admissible (a b α β : ℝ) : Set (ℝ → ℝ) :=
  {y | ContDiff ℝ 1 y ∧ y a = α ∧ y b = β}

lemma apm_m98J04_deriv_line (a b α β x : ℝ) :
    deriv (apm_m98J04_line a b α β) x = (β - α) / (b - a) := by
  unfold apm_m98J04_line
  have h : HasDerivAt
      (fun t : ℝ => α + ((β - α) / (b - a)) * (t - a))
      ((β - α) / (b - a)) x := by
    simpa using
      (((hasDerivAt_id x).sub_const a).const_mul ((β - α) / (b - a))).const_add α
  exact h.deriv

lemma apm_m98J04_arcLength_line (a b α β : ℝ) (hab : a < b) :
    apm_m98J04_arcLength a b (apm_m98J04_line a b α β) =
      (b - a) * Real.sqrt (1 + ((β - α) / (b - a)) ^ 2) := by
  unfold apm_m98J04_arcLength
  simp_rw [apm_m98J04_deriv_line a b α β]
  simp [intervalIntegral.integral_const]

/-- The computed graph length of the line is the Euclidean endpoint distance. -/
lemma apm_m98J04_arcLength_line_eq_sqrt (a b α β : ℝ) (hab : a < b) :
    apm_m98J04_arcLength a b (apm_m98J04_line a b α β) =
      Real.sqrt ((b - a) ^ 2 + (β - α) ^ 2) := by
  rw [apm_m98J04_arcLength_line a b α β hab]
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [← sq_eq_sq₀ (mul_nonneg hba.le (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- The endpoint identity needed for the graph-length lower bound. -/
lemma apm_m98J04_integral_deriv_eq_sub (a b : ℝ) (y : ℝ → ℝ)
    (hy : ContDiff ℝ 1 y) :
    ∫ x in a..b, deriv y x = y b - y a := by
  apply intervalIntegral.integral_deriv_eq_sub
  · intro x hx
    exact hy.differentiable one_ne_zero x
  · exact (hy.continuous_deriv le_rfl).intervalIntegrable a b

/-- The scalar graph arc-length integrand is a complex norm. -/
lemma apm_m98J04_norm_one_add_deriv_mul_I (y : ℝ → ℝ) (x : ℝ) :
    ‖((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I‖ =
      Real.sqrt (1 + (deriv y x) ^ 2) := by
  rw [Complex.norm_add_mul_I]
  norm_num

/-- Integrating the complex graph tangent records the endpoint displacement. -/
lemma apm_m98J04_integral_complex_tangent (a b : ℝ) (y : ℝ → ℝ)
    (hy : ContDiff ℝ 1 y) :
    ∫ x in a..b, (((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I) =
      ((b - a : ℝ) : ℂ) + ((y b - y a : ℝ) : ℂ) * Complex.I := by
  have hderiv : Continuous (deriv y) := hy.continuous_deriv le_rfl
  have h1 : IntervalIntegrable (fun _ : ℝ => ((1 : ℝ) : ℂ))
      MeasureTheory.volume a b := by
    exact continuous_const.intervalIntegrable a b
  have h2 : IntervalIntegrable
      (fun x : ℝ => ((deriv y x : ℝ) : ℂ) * Complex.I)
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add h1 h2]
  rw [show (∫ x in a..b, ((deriv y x : ℝ) : ℂ) * Complex.I) =
      (∫ x in a..b, ((deriv y x : ℝ) : ℂ)) * Complex.I from
    intervalIntegral.integral_mul_const Complex.I
      (fun x : ℝ => ((deriv y x : ℝ) : ℂ))]
  rw [intervalIntegral.integral_ofReal]
  rw [intervalIntegral.integral_ofReal]
  rw [apm_m98J04_integral_deriv_eq_sub a b y hy]
  simp

/-- The final topological stage of the fundamental lemma: a continuous
function which vanishes almost everywhere on an open interval vanishes at
every point of that interval. -/
lemma apm_m98J04_eq_zero_on_Ioo_of_ae
    (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo a b))
    (hae : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ioo a b → f x = 0) :
    ∀ x ∈ Ioo a b, f x = 0 := by
  have hae' : f =ᵐ[MeasureTheory.volume.restrict (Ioo a b)] (0 : ℝ → ℝ) := by
    change ∀ᵐ x ∂MeasureTheory.volume.restrict (Ioo a b), f x = 0
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact hae
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hf
    continuous_zero.continuousOn

theorem apm_m98j04 :
    (∀ (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ),
      a < b →
      ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ ↦ F p.1 p.2.1 p.2.2) →
      ContDiff ℝ 2 y →
      apm_m98J04_stationary F a b y →
      apm_m98J04_eulerLagrange F a b y) ∧
    ∀ (a b α β : ℝ), a < b →
      apm_m98J04_line a b α β ∈ apm_m98J04_admissible a b α β ∧
      ∀ y ∈ apm_m98J04_admissible a b α β,
        apm_m98J04_arcLength a b (apm_m98J04_line a b α β) ≤
          apm_m98J04_arcLength a b y := by
  constructor
  · /-
    PARTIAL boundary: deriving the pointwise Euler--Lagrange equation from the frozen
    stationarity predicate requires differentiating an interval integral with
    respect to the variation parameter, integration by parts, and a fundamental
    lemma for endpoint-zero `C¹` test variations. I searched Mathlib's
    `HasDerivAt`-under-integral, interval integration-by-parts, bump-function,
    and fundamental-lemma APIs; I did not find an assembled route matching this
    bespoke three-variable Lagrangian encoding.

    Closer hop 2 closes the entire arc-length conjunct below by routing the
    graph tangent through `ℂ`, using `Complex.norm_add_mul_I`,
    `intervalIntegral.integral_deriv_eq_sub`, and
    `intervalIntegral.norm_integral_le_integral_norm`.  A renewed source search
    found the dominated differentiation results in
    `Analysis/Calculus/ParametricIntervalIntegral.lean` and the interval
    integration-by-parts family in `IntegrationByParts.lean`.  These supply
    the first two analytic stages once their domination and integrability
    hypotheses are assembled.  No Mathlib or corpus declaration supplies the
    remaining fundamental lemma: from vanishing integrals against every
    endpoint-zero `C¹` test function, infer pointwise vanishing on `Ioo a b`.
    Consequently this first conjunct remains the precise open bridge.

    Closer hop 3 found a stronger distributional route that earlier searches
    missed: `ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives almost-
    everywhere vanishing from compactly supported smooth tests.  The compiled
    lemma `apm_m98J04_eq_zero_on_Ioo_of_ae` then upgrades that conclusion to
    pointwise vanishing on the open interval using
    `Measure.eqOn_open_of_ae_eq` and continuity.  Thus the fundamental-lemma
    endpoint itself is available.  What remains is the substantial preceding
    assembly: differentiate the frozen first variation, integrate by parts,
    and convert its interval-integral identity for endpoint-zero `C¹`
    variations into the whole-space compactly-supported-test hypothesis of
    the distribution theorem.
    -/
    sorry
  · intro a b α β hab
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · unfold apm_m98J04_line
        fun_prop
      · simp [apm_m98J04_line]
      · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
        simp [apm_m98J04_line, hba]
    · /-
      The complex number `1 + y' * I` packages the graph tangent without
      needing a custom Euclidean-product norm.  Its norm is the frozen
      arc-length integrand, while its integral is the endpoint displacement.
      -/
      intro y hy
      rw [apm_m98J04_arcLength_line_eq_sqrt a b α β hab]
      unfold apm_m98J04_arcLength
      rw [← Complex.norm_add_mul_I (b - a) (β - α)]
      calc
        ‖((b - a : ℝ) : ℂ) + ((β - α : ℝ) : ℂ) * Complex.I‖ =
            ‖∫ x in a..b,
              (((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I)‖ := by
              rw [apm_m98J04_integral_complex_tangent a b y hy.1]
              simp [hy.2.1, hy.2.2]
        _ ≤ ∫ x in a..b,
              ‖(((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab.le
        _ = ∫ x in a..b, Real.sqrt (1 + (deriv y x) ^ 2) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact apm_m98J04_norm_one_add_deriv_mul_I y x
