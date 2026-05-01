import Mathlib
import ApmCanaries.Frames.A01A09.Apm_v2_a01A09_1774988409275.Scratch

noncomputable section

namespace ApmCanaries.Frames.A01A09.Apm_v2_a01A09_1774988409275.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open scoped Real MeasureTheory Topology

open Complex MeasureTheory

lemma abs_exp_mul_real (z : ℂ) (t : ℝ) :
    Complex.abs (Complex.exp (z * (t : ℂ))) = Real.exp (z.re * t) := by
  simpa [Complex.abs_exp, Complex.mul_re, Complex.ofReal_im,
    Complex.ofReal_re, mul_comm, mul_left_comm, mul_assoc] using
    (Complex.abs_exp (z * (t : ℂ)))

/-- Absolute value of the Laplace kernel with the decaying `e^{-tz}` factor. -/
lemma abs_laplace_kernel (z : ℂ) (t : ℝ) :
    Complex.abs (Complex.exp (-(t : ℂ) * z)) = Real.exp (-z.re * t) := by
  simpa [neg_mul, abs_exp_mul_real, mul_comm] using
    abs_exp_mul_real (-z) t

/-- The closed half-line `[0,∞)` viewed as a measurable set. -/
def nonnegLine : Set ℝ := Set.Ici (0 : ℝ)

/-- Lebesgue measure restricted to `[0,∞)`. -/
def μ₊ : Measure ℝ := volume.restrict nonnegLine

/-- Right half-plane where the Laplace integral converges. -/
def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

/-- Laplace kernel `t ↦ e^{-tz}`. -/
def laplaceKernel (z : ℂ) (t : ℝ) : ℂ := Complex.exp (-(t : ℂ) * z)

/-- Laplace transform of `f` evaluated at `z`. -/
def laplaceTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t, f t * laplaceKernel z t ∂μ₊

/-- Package the standing hypotheses on `f`. -/
structure LaplaceData :=
  (p : ℝ)
  (hp : 1 < p)
  (f : ℝ → ℂ)
  (hf_meas : AEStronglyMeasurable f μ₊)
  (hf_lp : Memℒp f p μ₊)

/-- The Laplace integrand is absolutely integrable on vertical strips of the
right half-plane. -/
lemma laplace_integrand_integrable (data : LaplaceData) {z : ℂ}
    (hz : 0 < z.re) :
    Integrable (fun t => data.f t * laplaceKernel z t) μ₊ := by
  classical
  -- Sketch: apply Hölder with `f ∈ Lᵖ` and the exponential in `Lᵠ`.
  sorry

/-- Main claim (part 1): the Laplace transform is analytic on the right half-plane. -/
theorem laplace_transform_analytic (data : LaplaceData) :
    AnalyticOn ℂ (laplaceTransform data.f) rightHalfPlane := by
  classical
  -- Replace the derivative with termwise differentiation and apply dominated convergence.
  sorry

/-- Extra hypothesis ensuring the Laplace transform extends to an entire function. -/
def compactSupportOnHalfLine (f : ℝ → ℂ) : Prop :=
  ((Function.support f) ∩ nonnegLine).IsCompact

/-- Under compact support, the Laplace transform is entire (part 2). -/
theorem laplace_transform_entire_of_compact_support
    (f : ℝ → ℂ) (hf : compactSupportOnHalfLine f) :
    Analytic ℂ fun z => laplaceTransform f z := by
  classical
  -- Compact support ⇒ integrals converge uniformly on compact subsets of ℂ.
  sorry

end ApmCanaries.Frames.A01A09.Apm_v2_a01A09_1774988409275.Main
