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

theorem apm_a99j09 (f : ℝ → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ici (0 : ℝ)))) :
    DifferentiableOn ℂ (apm_a99j09_laplace f) apm_a99j09_rightHalfPlane := by
  -- SKIPPED: holomorphicity of Laplace transform on right half-plane for f∈Lᵖ.
  -- Key idea: Hölder gives |∫f(t)e^{-tz}dt| ≤ ‖f‖_p·‖e^{-t·Re(z)}‖_q < ∞ for Re(z)>0.
  -- Differentiate under integral: ∂/∂z gives -t·e^{-tz}, still Hölder-controlled.
  -- Blocker: parametric integral differentiation for complex Bochner integrals on
  -- unbounded domains with Lᵖ/Hölder domination is not readily available in Mathlib.
  -- APIs: `DifferentiableOn`, `MemLp`, `differentiableUnder_integral` — need to check.
  sorry
