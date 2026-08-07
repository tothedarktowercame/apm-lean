import Mathlib

/-!
# APM m98J05

## Statement repairs

The differentiation rule printed in part (b) omits the hypotheses needed for
integration by parts. It is stated for a differentiable function whose value
and derivative are integrable and whose boundary values vanish at both ends.
For parts (c)--(d), the initial datum is minimally strengthened to `C²`, with
its first two derivatives integrable, so that the displayed classical heat
equation and all Fourier transforms in the statement are defined.

## Encoding questions

The Fourier convention is fixed explicitly with kernel `exp (-i ξ x)`. The
heat equation is expressed by a real derivative in time equalling the second
real derivative in space. The initial condition is the right-hand limit as
`t → 0`, since the convolution formula is defined for `t > 0`.
-/

open Set Filter MeasureTheory intervalIntegral
open scoped Topology FourierTransform

/-- Fourier transform with the convention used in the source solution. -/
noncomputable def apm_m98J05_fourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))

lemma apm_m98J05_fourier_integrable (f : ℝ → ℂ) (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x => f x * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) := by
  have hg : Continuous
      (fun x : ℝ => Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) := by
    fun_prop
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with x
  simp [Complex.norm_exp]

/-- The custom unscaled convention is Mathlib's Fourier transform evaluated at
frequency `ξ / (2π)`. -/
lemma apm_m98J05_fourier_eq_mathlib (f : ℝ → ℂ) (ξ : ℝ) :
    apm_m98J05_fourier f ξ = 𝓕 f (ξ / (2 * Real.pi)) := by
  rw [apm_m98J05_fourier, Real.fourier_eq']
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [mul_comm]
  apply congrArg (fun z : ℂ => z * f x)
  apply congrArg Complex.exp
  have hi : inner ℝ x (ξ / (2 * Real.pi)) = x * (ξ / (2 * Real.pi)) := by
    rw [show ξ / (2 * Real.pi) = (ξ / (2 * Real.pi)) • (1 : ℝ) by simp,
      real_inner_smul_right]
    have hix : inner ℝ x (1 : ℝ) = x := by
      rw [real_inner_eq_re_inner, RCLike.inner_apply', conj_trivial, mul_one]
      rfl
    rw [hix]
    simp only [smul_eq_mul, mul_one]
    ring
  rw [hi]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The one-dimensional Gaussian heat kernel. -/
noncomputable def apm_m98J05_heatKernel (t x : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt (Real.pi * t))) * Real.exp (-(x ^ 2) / (4 * t))

/-- Convolution of the initial datum with the heat kernel. -/
noncomputable def apm_m98J05_heatSolution (f : ℝ → ℂ) (x t : ℝ) : ℂ :=
  ∫ y, f y * (apm_m98J05_heatKernel t (x - y) : ℂ)

theorem apm_m98j05 :
    (∀ (f f' : ℝ → ℂ),
      (∀ x, HasDerivAt f (f' x) x) →
      Integrable f → Integrable f' →
      Tendsto f atTop (nhds 0) → Tendsto f atBot (nhds 0) →
      ∀ ξ : ℝ,
        apm_m98J05_fourier f' ξ =
          Complex.I * (ξ : ℂ) * apm_m98J05_fourier f ξ) ∧
    ∀ f : ℝ → ℂ,
      ContDiff ℝ 2 f →
      Integrable f → Integrable (deriv f) → Integrable (iteratedDeriv 2 f) →
      let u := apm_m98J05_heatSolution f
      (∀ x : ℝ,
        Tendsto (fun t ↦ u x t) (nhdsWithin 0 (Ioi 0)) (nhds (f x))) ∧
      (∀ x t : ℝ, 0 < t →
        HasDerivAt (fun s ↦ u x s) (iteratedDeriv 2 (fun z ↦ u z t) x) t) ∧
      (∀ ξ t : ℝ, 0 < t →
        apm_m98J05_fourier (fun x ↦ u x t) ξ =
          apm_m98J05_fourier f ξ * Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2)) ∧
      (∀ ξ t : ℝ, 0 < t →
        HasDerivAt
          (fun s ↦ apm_m98J05_fourier (fun x ↦ u x s) ξ)
          (-((ξ : ℂ) ^ 2) * apm_m98J05_fourier (fun x ↦ u x t) ξ) t) := by
  constructor
  · intro f f' hder hf hf' _ _ ξ
    have hdiff : Differentiable ℝ f := fun x => (hder x).differentiableAt
    have heq : deriv f = f' := by
      funext x
      exact (hder x).deriv
    have hdint : Integrable (deriv f) := by simpa [heq] using hf'
    have hm := congrFun (Real.fourier_deriv hf hdiff hdint) (ξ / (2 * Real.pi))
    rw [apm_m98J05_fourier_eq_mathlib, apm_m98J05_fourier_eq_mathlib]
    rw [heq] at hm
    simp only [smul_eq_mul] at hm
    have hfac : (2 * (Real.pi : ℂ) * Complex.I * (ξ / (2 * Real.pi) : ℝ)) =
        Complex.I * (ξ : ℂ) := by
      push_cast
      field_simp [Real.pi_ne_zero]
    calc
      𝓕 f' (ξ / (2 * Real.pi)) =
          (2 * (Real.pi : ℂ) * Complex.I * (ξ / (2 * Real.pi) : ℝ)) *
            𝓕 f (ξ / (2 * Real.pi)) := hm
      _ = Complex.I * (ξ : ℂ) * 𝓕 f (ξ / (2 * Real.pi)) := by rw [hfac]
  · intro f hf2 hf hf' hf''
    have hmultiplier_ode (c : ℂ) (ξ t : ℝ) :
      HasDerivAt
        (fun s : ℝ ↦ c * Complex.exp (-(s : ℂ) * (ξ : ℂ) ^ 2))
        (-((ξ : ℂ) ^ 2) *
          (c * Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2))) t := by
      have hc : HasDerivAt
          (fun s : ℂ ↦ c * Complex.exp (-s * (ξ : ℂ) ^ 2))
          (-((ξ : ℂ) ^ 2) *
            (c * Complex.exp (-(t : ℂ) * (ξ : ℂ) ^ 2))) (t : ℂ) := by
        have hg : HasDerivAt (fun s : ℂ ↦ -s * (ξ : ℂ) ^ 2)
            (-((ξ : ℂ) ^ 2)) (t : ℂ) := by
          convert (hasDerivAt_id (x := (t : ℂ))).neg.mul_const ((ξ : ℂ) ^ 2) using 1 <;>
            ring
        convert ((Complex.hasDerivAt_exp _).comp (t : ℂ) hg).const_mul c using 1 <;>
          ring
      exact hc.comp_ofReal
    /-
  PARTIAL boundary (closer hop 1): the first frozen conjunct is now fully
  compiled. `apm_m98J05_fourier_eq_mathlib` identifies the raw convention with
  Mathlib's transform at `ξ/(2π)`; `Real.fourier_deriv` then proves the desired
  derivative multiplier after exact cancellation of the scale. Thus the
  whole-line complex integration-by-parts bridge has been routed around.

  The frequency-side scalar ODE for the claimed multiplier is also verified
  above, and `apm_m98J05_fourier_integrable` proves absolute integrability of
  every custom Fourier integrand. The remaining heat-solution theorem requires
  the Gaussian transform/convolution theorem with exact normalization,
  differentiation under the spatial and time improper integrals, and
  pointwise approximate-identity convergence.

  Mathlib provides `fourier_deriv` for its `2π` convention. Sibling `a01A10`
  proves the exact complex Gaussian transform from `fourierIntegral_gaussian`;
  sibling `a96A04` proves heat-kernel normalization, spatial differentiation,
  and an `L²` approximate-identity theorem. `ConstructionTargets.KernelAverage`
  and `ConstructionTargets.L2Translation` were also inspected. Adapting these
  results to a complex `L¹` datum, time derivative, and pointwise (rather than
  `L²`) initial convergence was not completed.
    -/
    sorry
