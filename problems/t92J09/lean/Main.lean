import Mathlib

/-!
# APM t92J09 — integrating `x dy ∧ dz` over the oriented unit sphere

## Statement repairs

None.

## Encoding questions

Mathlib does not yet provide integration of manifold differential forms over
oriented submanifolds. The pullback integral is therefore encoded concretely
using the standard outward-oriented spherical parametrization. The 2-form
itself is retained as the alternating map
`(p,u,v) ↦ p₀ (u₁v₂-u₂v₁)`, and is evaluated on the two parameter tangent
vectors before integration. Thus the surface form, pullback, orientation, and
surface integral all occur explicitly rather than being replaced by volume.
-/

open scoped Interval RealInnerProductSpace

noncomputable section

abbrev apm_t92J09_E3 := EuclideanSpace ℝ (Fin 3)

def apm_t92J09_sphere : Set apm_t92J09_E3 :=
  Metric.sphere 0 1

def apm_t92J09_inclusion : apm_t92J09_sphere → apm_t92J09_E3 :=
  Subtype.val

def apm_t92J09_omega
    (p u v : apm_t92J09_E3) : ℝ :=
  p 0 * (u 1 * v 2 - u 2 * v 1)

def apm_t92J09_param (θ φ : ℝ) : apm_t92J09_E3 :=
  WithLp.toLp 2 ![
    Real.sin θ * Real.cos φ,
    Real.sin θ * Real.sin φ,
    Real.cos θ]

def apm_t92J09_dTheta (θ φ : ℝ) : apm_t92J09_E3 :=
  WithLp.toLp 2 ![
    Real.cos θ * Real.cos φ,
    Real.cos θ * Real.sin φ,
    -Real.sin θ]

def apm_t92J09_dPhi (θ φ : ℝ) : apm_t92J09_E3 :=
  WithLp.toLp 2 ![
    -Real.sin θ * Real.sin φ,
    Real.sin θ * Real.cos φ,
    0]

def apm_t92J09_pullbackOmega (θ φ : ℝ) : ℝ :=
  apm_t92J09_omega (apm_t92J09_param θ φ)
    (apm_t92J09_dTheta θ φ) (apm_t92J09_dPhi θ φ)

def apm_t92J09_sphereIntegral : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    ∫ φ in (0 : ℝ)..2 * Real.pi, apm_t92J09_pullbackOmega θ φ

theorem apm_t92j09 :
    (∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        apm_t92J09_param θ φ ∈ apm_t92J09_sphere) ∧
    apm_t92J09_sphereIntegral = (4 / 3 : ℝ) * Real.pi := by
  sorry
