import Mathlib

/-!
# APM t94A09 — vector fields on two spheres and a torus

## Statement repairs

None.

## Encoding note

A smooth tangent field on an embedded sphere is represented by a smooth
ambient extension whose restriction is orthogonal to the radius.  For the
product torus `S¹ × S¹`, the two components are likewise tangent to their
circle factors.  Thus the actual vector fields, tangency, smoothness, and zero
sets are retained explicitly.
-/

open scoped ContDiff

noncomputable section

abbrev apm_t94a09_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t94a09_E4 := EuclideanSpace ℝ (Fin 4)
abbrev apm_t94a09_S2 := Metric.sphere (0 : apm_t94a09_E3) 1
abbrev apm_t94a09_S3 := Metric.sphere (0 : apm_t94a09_E4) 1
abbrev apm_t94a09_Torus := Circle × Circle

def apm_t94a09_SmoothSphereField
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Metric.sphere (0 : E) 1 → E) : Prop :=
  ∃ Vext : E → E, ContDiff ℝ ∞ Vext ∧
    ∀ p : Metric.sphere (0 : E) 1,
      Vext p = V p ∧ ⟪V p, (p : E)⟫_ℝ = 0

def apm_t94a09_SmoothTorusField
    (V : apm_t94a09_Torus → ℂ × ℂ) : Prop :=
  ∃ Vext : (ℂ × ℂ) → (ℂ × ℂ), ContDiff ℝ ∞ Vext ∧
    ∀ p : apm_t94a09_Torus,
      Vext (p.1, p.2) = V p ∧
      Complex.re (V p).1 * Complex.re p.1 +
          Complex.im (V p).1 * Complex.im p.1 = 0 ∧
      Complex.re (V p).2 * Complex.re p.2 +
          Complex.im (V p).2 * Complex.im p.2 = 0

theorem apm_t94a09 :
    (¬∃ V : apm_t94a09_S2 → apm_t94a09_E3,
      apm_t94a09_SmoothSphereField V ∧ ∀ p, V p ≠ 0) ∧
    (∃ V : apm_t94a09_S3 → apm_t94a09_E4,
      apm_t94a09_SmoothSphereField V ∧ ∀ p, V p ≠ 0) ∧
    (∃ V : apm_t94a09_Torus → ℂ × ℂ,
      apm_t94a09_SmoothTorusField V ∧ ∃! p, V p = 0) := by
  sorry
