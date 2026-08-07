import Mathlib

/-!
# APM t94A08 — a smooth and a degenerate conic in complex projective space

## Statement repairs

The second item reuses the name `Σ₁` in its premise but asks to prove that
`Σ₂` is not a manifold.  The second displayed locus is therefore named `Σ₂`.

## Encoding questions

Mathlib provides complex projectivization. Smoothness of each projective
hypersurface is encoded by the equivalent regular-cone criterion: the complex
derivative of its actual homogeneous quadratic is nonzero at every nonzero
point of the affine cone. This detects the crossing singularity of the
reducible second conic.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t94a08_C3 := Fin 3 → ℂ
abbrev apm_t94a08_CP2 := Projectivization ℂ apm_t94a08_C3

def apm_t94a08_quadratic1 (z : apm_t94a08_C3) : ℂ :=
  z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2

def apm_t94a08_quadratic2 (z : apm_t94a08_C3) : ℂ :=
  z 1 ^ 2 + z 2 ^ 2

def apm_t94a08_sigma1 : Set apm_t94a08_CP2 :=
  {p | apm_t94a08_quadratic1 (Projectivization.rep p) = 0}

def apm_t94a08_sigma2 : Set apm_t94a08_CP2 :=
  {p | apm_t94a08_quadratic2 (Projectivization.rep p) = 0}

def apm_t94a08_IsRealTwoManifold
    (q : apm_t94a08_C3 → ℂ) (S : Set apm_t94a08_CP2) : Prop :=
  S = {p | q (Projectivization.rep p) = 0} ∧
    ∀ z : apm_t94a08_C3, z ≠ 0 → q z = 0 → fderiv ℂ q z ≠ 0

theorem apm_t94a08 :
    apm_t94a08_IsRealTwoManifold apm_t94a08_quadratic1 apm_t94a08_sigma1 ∧
      ¬apm_t94a08_IsRealTwoManifold apm_t94a08_quadratic2 apm_t94a08_sigma2 := by
  sorry
