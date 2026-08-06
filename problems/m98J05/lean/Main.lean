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
open scoped Topology

/-- Fourier transform with the convention used in the source solution. -/
noncomputable def apm_m98J05_fourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))

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
  sorry
