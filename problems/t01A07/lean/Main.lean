import Mathlib

/-!
# APM t01A07

## Statement repairs

None.

## Encoding questions

Mathlib's projectivization has no smooth-manifold or oriented-intersection-number
API. The projective space and its quartic and line are encoded concretely; smoothness
is encoded by the equivalent regular-cone criterion. Only the oriented intersection
number operation itself is retained as an opaque, correctly typed placeholder.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t01a07_RP3 := ℙ ℝ (Fin 4 → ℝ)

def apm_t01a07_quartic (v : Fin 4 → ℝ) : ℝ :=
  v 0 ^ 4 - v 1 ^ 4 - v 2 ^ 4 + v 3 ^ 4

def apm_t01a07_surface : Set apm_t01a07_RP3 :=
  {p | apm_t01a07_quartic (Projectivization.rep p) = 0}

def apm_t01a07_line : Set apm_t01a07_RP3 :=
  {p | Projectivization.rep p 2 = 0 ∧ Projectivization.rep p 3 = 0}

def apm_t01a07_IsSmoothProjectiveHypersurface : Prop :=
  ∀ v : Fin 4 → ℝ, v ≠ 0 → apm_t01a07_quartic v = 0 →
    fderiv ℝ apm_t01a07_quartic v ≠ 0

opaque apm_t01a07_orientedIntersectionNumber
    (S L : Set apm_t01a07_RP3) : ℤ

theorem apm_t01a07 :
    apm_t01a07_IsSmoothProjectiveHypersurface ∧
      apm_t01a07_orientedIntersectionNumber
        apm_t01a07_surface apm_t01a07_line = 0 := by
  sorry
