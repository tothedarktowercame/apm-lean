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

-- (Lib: ConstructionTargets.YoungConvolution)
lemma m99A06_selfConvolution_eLpNorm_le {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    eLpNorm (m99A06SelfConvolution f) 1 volume ≤
      eLpNorm f 1 volume ^ 2 := by
  simpa [m99A06SelfConvolution,
    ConstructionTargets.YoungConvolution.convolution, pow_two] using
    (ConstructionTargets.YoungConvolution.young_convolution_inequality_one
      hf (memLp_one_iff_integrable.mpr hf))

/-- The two-input endpoint Young estimate in the raw integral notation used by
this problem.  This is the bilinear bound needed after polarizing the
self-convolution difference. -/
lemma m99A06_convolution_eLpNorm_le {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) :
    eLpNorm (fun x : ℝ ↦ ∫ y : ℝ, f (x - y) * g y) 1 volume ≤
      eLpNorm f 1 volume * eLpNorm g 1 volume := by
  simpa [ConstructionTargets.YoungConvolution.convolution] using
    (ConstructionTargets.YoungConvolution.young_convolution_inequality_one
      hf (memLp_one_iff_integrable.mpr hg))

lemma m99A06_sin_mul_selfConvolution_integrable {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    Integrable (fun x : ℝ => Real.sin x * m99A06SelfConvolution f x) volume := by
  exact (m99A06_selfConvolution_integrable hf).bdd_mul
    Real.continuous_sin.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using Real.abs_sin_le_one x)

lemma m99A06_sin_mul_eLpNorm_le (p : ENNReal) (g : ℝ → ℝ) :
    eLpNorm (fun x : ℝ ↦ Real.sin x * g x) p volume ≤
      eLpNorm g p volume := by
  apply eLpNorm_mono_ae
  filter_upwards with x
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg (g x)) (Real.abs_sin_le_one x)

lemma m99A06_quadraticTerm_eLpNorm_le {f : ℝ → ℝ}
    (hf : Integrable f volume) :
    eLpNorm (fun x : ℝ ↦ Real.sin x * m99A06SelfConvolution f x) 1 volume ≤
      eLpNorm f 1 volume ^ 2 := by
  exact (m99A06_sin_mul_eLpNorm_le 1 (m99A06SelfConvolution f)).trans
    (m99A06_selfConvolution_eLpNorm_le hf)

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
  Boundary (closer hop 2): integrability of the Gaussian forcing and of the sine-multiplied
  quadratic convolution term, needed to define the fixed-point self-map on
  `L¹`, is proved above. Closer hop 1 extracts Gaussian integrability into
  `m99A06_gaussian_integrable` and proves the complete raw self-map
  integrability statement `m99A06_fixedPointMap_integrable`. This hop
  specializes the sharp endpoint estimate from
  `ConstructionTargets.YoungConvolution` to prove
  `m99A06_selfConvolution_eLpNorm_le`, proves that multiplication by sine is
  nonexpansive in every `eLpNorm`, and combines them in
  `m99A06_quadraticTerm_eLpNorm_le`:
  `‖sin(·) * (f*f)‖₁ ≤ ‖f‖₁²`. Thus the quadratic self-map bound is closed.

  Completing the
  theorem requires
  working in the complete `L¹` quotient space, transporting the raw convolution
  to representatives, proving the two-input quadratic Lipschitz estimate, and
  applying Banach's fixed-point theorem on a closed ball before
  selecting a representative satisfying the equation almost everywhere. I
  searched Mathlib's `L1`, convolution, bounded multiplier, closed-ball, and
  contraction APIs and used `ConstructionTargets.YoungConvolution.convolution_memLp`;
  I did not complete the quotient/representative bridge
  to the frozen raw-function predicate `IsM99A06Solution` in this pass.

  Closer hop 3 compiles the missing genuinely bilinear estimate as
  `m99A06_convolution_eLpNorm_le`, specializing
  `young_convolution_inequality_one` to two distinct raw integrable inputs.
  Consequently the two-input quadratic Lipschitz estimate is reduced to the
  pointwise polarization identity
  `f*f - g*g = (f-g)*f + g*(f-g)`, the `eLpNorm` triangle inequality, and
  representative bookkeeping.  Searches of `LEMMA-INDEX.md`, the closed
  corpus, Mathlib's `L1` quotient API, construction libraries, and git history
  found no bundled convolution operation on `L1` that both respects a.e.
  representatives and exposes the frozen raw integral.  The quotient
  construction, contraction on a closed ball, and representative extraction
  therefore remain open.
  -/
  sorry
