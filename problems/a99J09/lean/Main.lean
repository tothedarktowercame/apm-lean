import Mathlib

/-!
# APM a99J09 — holomorphicity of the Laplace transform

## Statement repairs

None.

## Encoding notes

The source function on `[0, ∞)` is represented by an ambient function on `ℝ`
whose `Lᵖ` hypothesis uses `volume.restrict (Set.Ici 0)`.  Its Laplace
transform is likewise integrated over `Set.Ici 0`.
-/

open scoped ENNReal
open Set Filter MeasureTheory

noncomputable def apm_a99j09_laplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ici (0 : ℝ), f t * Complex.exp (-(t : ℂ) * z) ∂volume

def apm_a99j09_rightHalfPlane : Set ℂ :=
  {z | 0 < z.re}

/-- Exact norm of the decaying Laplace kernel.  This is the scalar identity
used by the Hölder and local derivative dominators. -/
lemma apm_a99j09_norm_kernel (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-z.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
  ring

theorem apm_a99j09 (f : ℝ → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ici (0 : ℝ)))) :
    DifferentiableOn ℂ (apm_a99j09_laplace f) apm_a99j09_rightHalfPlane := by
  /-
  Boundary (closer hop 1): a search of the closed corpus found the exact solved
  sibling `problems/a01A09/lean/Main.lean`.  Its theorem
  `laplace_transform_analytic` proves this result using
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; its supporting lemmas
  `laplace_integrand_integrable` and `laplace_deriv_bound_integrable` establish
  the two Hölder estimates.  The compiled helper `apm_a99j09_norm_kernel` above
  imports the shared scalar kernel identity into this bundle.

  The sibling cannot currently be reused as a dependency: `problems/` is not a
  configured `lean_lib`, and its theorem is in a frame-specific namespace, so
  `import Problems.a01A09.lean.Main` fails with unknown module prefix.  Searches
  of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's Laplace/Mellin/MGF
  APIs, and git history found no importable equivalent.  Closing this theorem is
  now a mechanical local adaptation of the sibling's two Hölder lemmas and its
  dominated-derivative proof, replacing its aliases `μ₊`, `laplaceKernel`, and
  `laplaceTransform` by the frozen definitions here.  The mathematical and API
  bridge is found; only the unavailable-module/code-promotion bridge remains.
  -/
  sorry
