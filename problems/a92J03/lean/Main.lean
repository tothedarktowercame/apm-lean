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
open scoped Topology

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

    **SORRY BOUNDARY:** Mathlib's `Real.tendsto_integral_exp_smul_cocompact`
    proves Riemann-Lebesgue for `∫ 𝐞(-(v*w)) • f(v) dv` (with `2π` in the
    exponent). The problem's convention `∫ f(x) exp(ixξ) dx` differs.
    The identity connecting them is:
    `exp(ixξ) = 𝐞(x · (-ξ/(2π)))` (since `𝐞(y) = exp(2πiy)`).
    As `|ξ| → ∞`, `|w| = |ξ|/(2π) → ∞`, preserving cocompact.
    The change of variables requires `MeasureTheory.integral_comp` or a
    `ContinuousLinearEquiv` argument, plus showing `cocompact` is preserved
    under the homeomorphism `ξ ↦ -ξ/(2π)`.
    Tried: `Real.tendsto_integral_exp_smul_cocompact` gives
    `Tendsto (fun w => ∫ v, 𝐞(-(v*w)) • f v) (cocompact ℝ) (𝓝 0)`.
    Substituting `w ↦ -ξ/(2π)` and using `𝐞(-v*(-ξ/(2π))) = exp(ivξ)`
    requires unfolding `Real.fourierChar`, `Circle.smul`, and the
    `ContinuousLinearEquiv` for cocompact map. -/
theorem fourierTransform_tendsto_zero {f : ℝ → ℂ} (hf : Integrable f volume) :
    Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0) := by
  -- Mathlib proves: Tendsto (fun w => ∫ v, 𝐞(-(v*w)) • f v) (cocompact ℝ) (𝓝 0)
  -- Our f̂(ξ) = ∫ f(x) exp(ixξ) dx
  -- Key identity: exp(ixξ) = 𝐞(x * ξ/(2π))  [since 𝐞(y) = exp(2πiy)]
  -- So f̂(ξ) = ∫ f(x) 𝐞(x * ξ/(2π)) dx
  -- Mathlib's version at w = -ξ/(2π):
  --   ∫ f(v) 𝐞(-(v * (-ξ/(2π)))) dv = ∫ f(v) 𝐞(v*ξ/(2π)) dv = f̂(ξ)
  -- The map ξ ↦ -ξ/(2π) sends cocompact to cocompact (homeomorphism).
  -- **SORRY BOUNDARY:** Connecting the two Fourier conventions requires:
  -- (1) Showing 𝐞(-(v * (-ξ/(2π)))) • f v = f v * exp(ivξ) as complex numbers
  --     [requires unfolding Real.fourierChar, Circle.smul_def, algebraic manipulation]
  -- (2) Showing the composition Tendsto with the cocompact-preserving map
  --     ξ ↦ -ξ/(2π) [requires Filter.Tendsto.comp + cocompact_le_cocompact
  --     under proper maps or homeomorphisms]
  -- Both are mathematically straightforward but require navigating Mathlib's
  -- AddChar/Circle/fourierChar API and the cocompact filter composition.
  sorry

/-- **Full theorem:** `f̂` is continuous, bounded by `‖f‖₁`, and vanishes at ∞. -/
theorem fourier_maps_L1_to_C0 {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (fourierTransform f) ∧
    (∀ ξ, ‖fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume) ∧
    Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0) :=
  ⟨fourierTransform_continuous hf,
   fun ξ => fourierTransform_norm_le hf ξ,
   fourierTransform_tendsto_zero hf⟩

end ApmCanaries.A92J03
