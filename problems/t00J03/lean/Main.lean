import Mathlib

/-!
# APM t00J03

## Statement repairs

The final occurrence of `ℝ²` in the source is read as `ℝ² \ {0}`, the domain
of the quotient map and of the displayed angle form.  At the origin its
denominator vanishes, so the unrepaired wording is not meaningful.

## Encoding questions

`RP¹` is the actual real projectivization of `ℝ²` with its quotient topology,
and the pullback is evaluated on actual points and tangent vectors of the
punctured plane.  Mathlib does not package smooth differential forms and their
integration on quotient manifolds in a usable common interface, so the type of
smooth one-forms, pullback evaluation, and oriented integral are isolated as
typed primitives.  The displayed form itself remains fully explicit.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t00J03_Plane := Fin 2 → ℝ
abbrev apm_t00J03_PuncturedPlane := {x : apm_t00J03_Plane // x ≠ 0}
abbrev apm_t00J03_RP1 := Projectivization ℝ apm_t00J03_Plane

noncomputable instance : TopologicalSpace apm_t00J03_RP1 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ apm_t00J03_Plane)))

/-- Smooth real one-forms on the actual projective line. -/
opaque apm_t00J03_OneForm : Type

/-- Evaluation of the pullback of a projective one-form to `ℝ² \ {0}`. -/
opaque apm_t00J03_pullbackEval
    (eta : apm_t00J03_OneForm)
    (x : apm_t00J03_PuncturedPlane) (v : apm_t00J03_Plane) : ℝ

/-- The two orientations of the real projective line. -/
inductive apm_t00J03_Orientation
  | anglePositive
  | angleNegative

/-- Integral of a smooth one-form over `RP¹` with the indicated orientation. -/
opaque apm_t00J03_integral
    (orientation : apm_t00J03_Orientation)
    (eta : apm_t00J03_OneForm) : ℝ

/-- The angle form `(x⁰ dx¹ - x¹ dx⁰) / ((x⁰)² + (x¹)²)`. -/
def apm_t00J03_angleFormValue
    (x : apm_t00J03_PuncturedPlane) (v : apm_t00J03_Plane) : ℝ :=
  (x.1 0 * v 1 - x.1 1 * v 0) / (x.1 0 ^ 2 + x.1 1 ^ 2)

theorem apm_t00j03 :
    ∃ eta : apm_t00J03_OneForm,
      (∀ (x : apm_t00J03_PuncturedPlane) (v : apm_t00J03_Plane),
        apm_t00J03_pullbackEval eta x v = apm_t00J03_angleFormValue x v) ∧
      apm_t00J03_integral .anglePositive eta = Real.pi ∧
      apm_t00J03_integral .angleNegative eta = -Real.pi := by
  sorry
