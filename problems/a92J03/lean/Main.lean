import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# APM a92J03: The Fourier transform maps L¹ to C₀ (Riemann-Lebesgue)

**Problem.** For `f ∈ L¹(ℝ)`, define `f̂(ξ) = ∫ f(x) e^{ixξ} dx`. Prove:
(a) `f̂` is continuous,
(b) `‖f̂‖_∞ ≤ ‖f‖₁`,
(c) Deduce: `f ↦ f̂` maps `L¹(ℝ)` into `C₀(ℝ)`.

## Statement repair note

The informal proof proposes a `fourierTransform` using `exp(I * x * ξ)`.
Mathlib's `𝓕` uses `exp(-2πivw * I)`. We define our own `fourierTransform`
following the problem's convention and prove the three parts directly:
- Part (a): DCT via `continuous_of_dominated`.
- Part (b): `norm_integral_le_integral_norm` + `|e^{ixξ}| = 1`.
- Part (c): Riemann-Lebesgue via Mathlib's existing lemma.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Complex Set Filter
open scoped Topology FourierTransform

namespace ApmCanaries.A92J03

/-- The Fourier transform: `f̂(ξ) = ∫ f(x) e^{ixξ} dx`. -/
noncomputable def fourierTransform (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (I * x * ξ) ∂volume

/-! ## Part (b): Norm bound -/

/-- **Part (b):** `‖f̂(ξ)‖ ≤ ∫ ‖f(x)‖ dx`. -/
theorem fourierTransform_norm_le {f : ℝ → ℂ} (hf : Integrable f volume) (ξ : ℝ) :
    ‖fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume := by
  show ‖∫ x, f x * Complex.exp (I * x * ξ) ∂volume‖ ≤ ∫ x, ‖f x‖ ∂volume
  calc ‖∫ x, f x * Complex.exp (I * x * ξ) ∂volume‖
      ≤ ∫ x, ‖f x * Complex.exp (I * x * ξ)‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ ∂volume := by
        congr 1 with x
        rw [norm_mul]
        have hexp : ‖Complex.exp (I * (x : ℂ) * ξ)‖ = 1 := by
          have key : I * (x : ℂ) * ξ = ↑(x * ξ) * I := by
            rw [Complex.ext_iff]
            constructor <;> simp
          rw [key]
          exact Complex.norm_exp_ofReal_mul_I (x * ξ)
        rw [hexp, mul_one]

/-! ## Part (a): Continuity -/

/-- **Part (a):** `f̂` is continuous.

    Uses `continuous_of_dominated`: the integrand `f(x) e^{ixξ}` is continuous
    in `ξ` for each `x`, dominated by `‖f(x)‖` (since `|e^{ixξ}| = 1`). -/
theorem fourierTransform_continuous {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (fourierTransform f) := by
  unfold fourierTransform
  refine continuous_of_dominated (fun ξ => ?_) ?_ hf.norm ?_
  · exact hf.aestronglyMeasurable.mul
      ((Complex.continuous_exp.comp <| by fun_prop).aestronglyMeasurable)
  · intro ξ
    apply ae_of_all volume fun x => ?_
    rw [norm_mul]
    have hexp : ‖Complex.exp (I * (x : ℂ) * ξ)‖ = 1 := by
      have key : I * (x : ℂ) * ξ = ↑(x * ξ) * I := by
        rw [Complex.ext_iff]
        constructor <;> simp
      rw [key]
      exact Complex.norm_exp_ofReal_mul_I (x * ξ)
    rw [hexp, mul_one]
  · apply ae_of_all volume fun x => ?_
    fun_prop

/-! ## Part (c): Riemann-Lebesgue lemma -/

/-- **Part (c):** For any `f ∈ L¹(ℝ)`, `f̂(ξ) → 0` as `|ξ| → ∞`.

    This transports `Real.tendsto_integral_exp_smul_cocompact` across the
    nonzero scaling `ξ ↦ -(2π)⁻¹ ξ`. Unfolding the Fourier character shows
    that Mathlib's normalized integrand at the scaled frequency is exactly
    `f x * exp (I * x * ξ)`. -/
theorem fourierTransform_tendsto_zero {f : ℝ → ℂ} (hf : Integrable f volume) :
    Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0) := by
  have heq : fourierTransform f =
      fun ξ : ℝ => ∫ x : ℝ, 𝐞 (-(x * ((-(2 * Real.pi)⁻¹) * ξ))) • f x := by
    funext ξ
    unfold fourierTransform
    congr with x
    rw [Circle.smul_def, Real.fourierChar_apply]
    ring_nf
    field_simp [Real.pi_ne_zero]
    rw [smul_eq_mul]
    conv_rhs => rw [mul_comm]
    apply congrArg (fun z : ℂ => f x * Complex.exp z)
    push_cast
    ring
  have hscale :
      Tendsto (fun ξ : ℝ => (-(2 * Real.pi)⁻¹) * ξ) (cocompact ℝ) (cocompact ℝ) :=
    Filter.tendsto_cocompact_mul_left₀
      (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
  rw [heq]
  exact (Real.tendsto_integral_exp_smul_cocompact f).comp hscale

/-- **Full theorem:** `f̂` is continuous, bounded by `‖f‖₁`, and vanishes at ∞. -/
theorem fourier_maps_L1_to_C0 {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (fourierTransform f) ∧
    (∀ ξ, ‖fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume) ∧
    Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0) :=
  ⟨fourierTransform_continuous hf,
   fun ξ => fourierTransform_norm_le hf ξ,
   fourierTransform_tendsto_zero hf⟩

end ApmCanaries.A92J03

/-- The Fourier-transform assignment on `L¹(ℝ)` is linear, takes values in
`C₀(ℝ)`, and satisfies the requested uniform norm bound. -/
theorem apm_a92j03 :
    (∀ f : ℝ → ℂ, Integrable f volume →
      Continuous (ApmCanaries.A92J03.fourierTransform f)) ∧
    (∀ f : ℝ → ℂ, Integrable f volume → ∀ ξ : ℝ,
      ‖ApmCanaries.A92J03.fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume) ∧
    (∀ f : ℝ → ℂ, Integrable f volume →
      Tendsto (ApmCanaries.A92J03.fourierTransform f) (cocompact ℝ) (nhds 0)) ∧
    (∀ f g : ℝ → ℂ, Integrable f volume → Integrable g volume →
      ApmCanaries.A92J03.fourierTransform (f + g) =
        ApmCanaries.A92J03.fourierTransform f +
          ApmCanaries.A92J03.fourierTransform g) ∧
    (∀ c : ℂ, ∀ f : ℝ → ℂ, Integrable f volume →
      ApmCanaries.A92J03.fourierTransform (c • f) =
        c • ApmCanaries.A92J03.fourierTransform f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    exact ApmCanaries.A92J03.fourierTransform_continuous hf
  · intro f hf ξ
    exact ApmCanaries.A92J03.fourierTransform_norm_le hf ξ
  · intro f hf
    exact ApmCanaries.A92J03.fourierTransform_tendsto_zero hf
  · intro f g hf hg
    funext ξ
    unfold ApmCanaries.A92J03.fourierTransform
    have hmul (u : ℝ → ℂ) (hu : Integrable u volume) :
        Integrable (fun x : ℝ => u x * Complex.exp (I * x * ξ)) volume := by
      apply hu.mul_bdd
      · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · filter_upwards [] with x
        have key : I * (x : ℂ) * ξ = ↑(x * ξ) * I := by
          apply Complex.ext <;> simp
        rw [key, Complex.norm_exp_ofReal_mul_I]
    rw [show (∫ x, (f + g) x * Complex.exp (I * x * ξ) ∂volume) =
        ∫ x, (f x * Complex.exp (I * x * ξ) +
          g x * Complex.exp (I * x * ξ)) ∂volume by
          congr 1 with x
          simp [add_mul]]
    exact integral_add (hmul f hf) (hmul g hg)
  · intro c f hf
    funext ξ
    unfold ApmCanaries.A92J03.fourierTransform
    rw [show (∫ x, (c • f) x * Complex.exp (I * x * ξ) ∂volume) =
        ∫ x, c • (f x * Complex.exp (I * x * ξ)) ∂volume by
          congr 1 with x
          simp [smul_eq_mul, mul_assoc]]
    exact integral_smul c _
