import Mathlib

/-!
# APM m02J01

## Statement repairs

The spelling `primative` in the source is read as `primitive`; no mathematical
change is made.

## Encoding notes

The statement uses Mathlib's genuine LF-topological test-function and
distribution spaces.  Distributional differentiation is exposed by its
defining action on the pointwise derivative of every bundled test function.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

def apm_m02j01_IsDistributionalDerivative
    (v u : Distribution (⊤ : Opens ℝ) ℝ ⊤) : Prop :=
  ∀ φ dφ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
    (∀ x : ℝ, dφ x = deriv (φ : ℝ → ℝ) x) → u φ = -v dφ

/-- The derivative of a test function has total integral zero. This is the
function-level necessity direction of part (a). -/
lemma apm_m02j01_integral_deriv_testFunction_eq_zero
    (ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    ∫ x : ℝ, deriv (ψ : ℝ → ℝ) x = 0 := by
  have hdiff : ContDiff ℝ 1 (ψ : ℝ → ℝ) := ψ.contDiff.of_le (by simp)
  have hcompact : HasCompactSupport (ψ : ℝ → ℝ) := ψ.hasCompactSupport
  have hint : Integrable (deriv (ψ : ℝ → ℝ)) :=
    hdiff.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hcompact.deriv
  rw [← integral_add_compl measurableSet_Iic hint, compl_Iic]
  rw [hcompact.integral_Iic_deriv_eq hdiff 0,
    hcompact.integral_Ioi_deriv_eq hdiff 0]
  ring

lemma apm_m02j01_integral_eq_zero_of_eq_deriv
    (φ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤)
    (h : ∀ x : ℝ, φ x = deriv (ψ : ℝ → ℝ) x) :
    ∫ x : ℝ, φ x = 0 := by
  calc
    ∫ x : ℝ, φ x = ∫ x : ℝ, deriv (ψ : ℝ → ℝ) x :=
      integral_congr_ae (Filter.Eventually.of_forall h)
    _ = 0 := apm_m02j01_integral_deriv_testFunction_eq_zero ψ

/-- The ordinary interval-integral primitive of a test function is smooth and
has the original function as its derivative. -/
lemma apm_m02j01_primitive_smooth
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    let P : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, φ t
    ContDiff ℝ ∞ P ∧ ∀ x : ℝ, deriv P x = φ x := by
  let P : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, φ t
  have hderiv (x : ℝ) : HasDerivAt P (φ x) x := by
    exact intervalIntegral.integral_hasDerivAt_right
      (φ.contDiff.continuous.intervalIntegrable 0 x)
      (φ.contDiff.continuous.stronglyMeasurableAtFilter volume (nhds x))
      φ.contDiff.continuous.continuousAt
  have hderiv_eq : deriv P = (φ : ℝ → ℝ) := by
    funext x
    exact (hderiv x).deriv
  refine ⟨(contDiff_infty_iff_deriv.mpr ⟨?_, ?_⟩), fun x => congrFun hderiv_eq x⟩
  · exact fun x => (hderiv x).differentiableAt
  · rw [hderiv_eq]
    exact φ.contDiff

theorem apm_m02j01 :
    (∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
      (∫ x : ℝ, φ x) = 0 ↔
        ∃ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
          ∀ x : ℝ, φ x = deriv (ψ : ℝ → ℝ) x) ∧
    (∀ u : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∃ v : Distribution (⊤ : Opens ℝ) ℝ ⊤,
        apm_m02j01_IsDistributionalDerivative v u) ∧
    (∀ u v₁ v₂ : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      apm_m02j01_IsDistributionalDerivative v₁ u →
      apm_m02j01_IsDistributionalDerivative v₂ u →
      ∃ c : ℝ, ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        (v₁ - v₂) φ = c * ∫ x : ℝ, φ x) := by
  /-
  SKIPPED (test-function LF-topology API boundary). The mathematical proof
  needs a continuous linear primitive operator on the codimension-one space of
  compactly supported smooth functions with integral zero. Searches of
  Mathlib's `TestFunction` and `Distribution` APIs found the endpoint identity
  `HasCompactSupport.integral_Ioi_deriv_eq`, but no bundled primitive operator
  that preserves compact support and is continuous for the test-function
  LF topology, nor a theorem that distributional differentiation on `ℝ` is
  surjective with constants as its kernel.

  Closer hop 1 compiles the necessity direction of part (a).
  `apm_m02j01_integral_deriv_testFunction_eq_zero` splits the whole-line
  integral at zero and combines `HasCompactSupport.integral_Iic_deriv_eq` with
  `HasCompactSupport.integral_Ioi_deriv_eq`; the endpoint values cancel.
  `apm_m02j01_integral_eq_zero_of_eq_deriv` then transports this result across
  the pointwise derivative identity. Thus every test-function derivative now
  formally has total integral zero.

  Closer hop 2 now compiles the reverse FTC/smoothness component as
  `apm_m02j01_primitive_smooth`: the explicit interval-integral primitive is
  globally `C∞` and its derivative is pointwise equal to the original test
  function. This uses `intervalIntegral.integral_hasDerivAt_right` and
  `contDiff_infty_iff_deriv`, neither of which was exploited by hop 1.

  The remaining function-level step is to use compact support and the
  zero-total-integral hypothesis to show this primitive vanishes on both
  tails, then bundle it as a `TestFunction`. Parts (b) and (c) further require
  bundling that
  construction as a continuous linear map before it can be transposed to a
  `Distribution`; this bridge is not supplied by the abstract distribution
  derivative API. Renewed searches of `LEMMA-INDEX.md`, closed artifacts,
  `ConstructionTargets/`, `TestFunction`, and `Distribution` sources found no
  compiled sibling route or reusable LF-continuity theorem, and the
  frozen statement remains unchanged.
  -/
  sorry
