import Mathlib
import ConstructionTargets.YoungConvolution

/-! # APM m99A06: a small convolution-quadratic equation in `L¹`

## Statement repairs

None.

## Encoding note

An `L¹` function is determined only almost everywhere, so the functional
equation is stated almost everywhere with respect to Lebesgue measure.  This is
the canonical faithful reading of an equation whose unknown is required only to
belong to `L¹(ℝ)`.
-/

open Filter MeasureTheory

noncomputable section

def m99A06SelfConvolution (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f (x - y) * f y

def IsM99A06Solution (ε : ℝ) (f : ℝ → ℝ) : Prop :=
  Integrable f ∧
  ∀ᵐ x : ℝ ∂volume,
    f x + Real.sin x * m99A06SelfConvolution f x =
      ε * Real.exp (-|x| ^ 2)

-- (Lib: ConstructionTargets.YoungConvolution)
lemma m99A06_selfConvolution_integrable {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    Integrable (m99A06SelfConvolution f) volume := by
  rw [← memLp_one_iff_integrable]
  simpa [m99A06SelfConvolution,
    ConstructionTargets.YoungConvolution.convolution] using
    (ConstructionTargets.YoungConvolution.convolution_memLp
      (p := (1 : ENNReal)) (by norm_num) (by norm_num) hf
      (memLp_one_iff_integrable.mpr hf))

lemma m99A06_sin_mul_selfConvolution_integrable {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    Integrable (fun x : ℝ => Real.sin x * m99A06SelfConvolution f x) volume := by
  exact (m99A06_selfConvolution_integrable hf).bdd_mul
    Real.continuous_sin.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using Real.abs_sin_le_one x)

lemma m99A06_gaussian_integrable :
    Integrable (fun x : ℝ => Real.exp (-|x| ^ 2)) volume := by
  simpa [sq_abs] using
    (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))

/-- The raw-function fixed-point expression is integrable whenever its input
is integrable. -/
lemma m99A06_fixedPointMap_integrable (ε : ℝ) {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    Integrable (fun x : ℝ =>
      ε * Real.exp (-|x| ^ 2) -
        Real.sin x * m99A06SelfConvolution f x) volume := by
  exact (m99A06_gaussian_integrable.const_mul ε).sub
    (m99A06_sin_mul_selfConvolution_integrable hf)

theorem apm_m99a06 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ,
      0 < ε → ε < ε₀ → ∃ f : ℝ → ℝ, IsM99A06Solution ε f := by
  have hforcing : Integrable (fun x : ℝ ↦ Real.exp (-|x| ^ 2)) := by
    exact m99A06_gaussian_integrable
  /-
  Boundary: integrability of the Gaussian forcing and of the sine-multiplied
  quadratic convolution term, needed to define the fixed-point self-map on
  `L¹`, is proved above. Closer hop 1 extracts Gaussian integrability into
  `m99A06_gaussian_integrable` and proves the complete raw self-map
  integrability statement `m99A06_fixedPointMap_integrable`. Completing the
  theorem requires
  working in the complete `L¹` quotient space, transporting the raw convolution
  to representatives, proving Young's inequality and the quadratic Lipschitz
  estimate, and applying Banach's fixed-point theorem on a closed ball before
  selecting a representative satisfying the equation almost everywhere. I
  searched Mathlib's `L1`, convolution, bounded multiplier, closed-ball, and
  contraction APIs and used `ConstructionTargets.YoungConvolution.convolution_memLp`;
  I did not complete the quotient/representative bridge
  to the frozen raw-function predicate `IsM99A06Solution` in this pass.
  -/
  sorry
