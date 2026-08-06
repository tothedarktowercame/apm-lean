import Mathlib

/-!
# APM t00J03

## Statement repairs

The final occurrence of `ℝ²` in the source is read as `ℝ² \ {0}`, the domain
of the quotient map and of the displayed angle form. At the origin its
denominator vanishes, so the unrepaired wording is not meaningful.

The former conclusion used opaque one-form, pullback, and integral constants.
They are replaced by a concrete quotient of tangent representatives and
ordinary interval integrals along the two orientations of an explicit
half-circle parametrization of the actual real projective line.
-/

open Set
open scoped Interval
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t00j03_Plane := Fin 2 → ℝ
abbrev apm_t00j03_PuncturedPlane := {x : apm_t00j03_Plane // x ≠ 0}
abbrev apm_t00j03_RP1 := Projectivization ℝ apm_t00j03_Plane

noncomputable instance : TopologicalSpace apm_t00j03_RP1 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ apm_t00j03_Plane)))

def apm_t00j03_projectivize (x : apm_t00j03_PuncturedPlane) : apm_t00j03_RP1 :=
  Projectivization.mk' ℝ x

/-- Changing a projective tangent representative permits rescaling both
components and adding a radial vector to the tangent component. -/
inductive apm_t00j03_tangentRel :
    (apm_t00j03_PuncturedPlane × apm_t00j03_Plane) →
      (apm_t00j03_PuncturedPlane × apm_t00j03_Plane) → Prop
  | change (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane)
      (lam a : ℝ) (hlam : lam ≠ 0) :
      apm_t00j03_tangentRel (x, v)
        (⟨lam • x.1, smul_ne_zero hlam x.2⟩, lam • v + a • x.1)

def apm_t00j03_ProjectiveTangent :=
  Quotient (Relation.EqvGen.setoid apm_t00j03_tangentRel)

/-- The angle form `(x⁰ dx¹ - x¹ dx⁰) / ((x⁰)² + (x¹)²)`. -/
def apm_t00j03_angleFormValue
    (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane) : ℝ :=
  (x.1 0 * v 1 - x.1 1 * v 0) / (x.1 0 ^ 2 + x.1 1 ^ 2)

def apm_t00j03_circlePoint (θ : ℝ) : apm_t00j03_PuncturedPlane :=
  ⟨![Real.cos θ, Real.sin θ], by
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    nlinarith [Real.sin_sq_add_cos_sq θ]⟩

def apm_t00j03_circleVelocity (θ : ℝ) : apm_t00j03_Plane :=
  ![-Real.sin θ, Real.cos θ]

def apm_t00j03_tangentClass (θ : ℝ) : apm_t00j03_ProjectiveTangent :=
  Quotient.mk _ (apm_t00j03_circlePoint θ, apm_t00j03_circleVelocity θ)

theorem apm_t00j03 :
    Function.Surjective apm_t00j03_projectivize ∧
    ∃ eta : apm_t00j03_ProjectiveTangent → ℝ,
      (∀ (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane),
        eta (Quotient.mk _ (x, v)) = apm_t00j03_angleFormValue x v) ∧
      (∫ θ in (0 : ℝ)..Real.pi, eta (apm_t00j03_tangentClass θ)) = Real.pi ∧
      (∫ θ in Real.pi..(0 : ℝ), eta (apm_t00j03_tangentClass θ)) = -Real.pi := by
  sorry
