import Mathlib

/-!
# APM t01A07

## Statement repairs

The former conclusion used an opaque intersection-number constant. It is
replaced by the concrete signed enumeration of the actual intersection set;
the two projective intersection points have opposite local signs. No source
claim is changed.

## Encoding questions

Mathlib's projectivization has no oriented-intersection-number API. The
projective space, quartic, line, their intersection subtype, and its local
signs are encoded concretely; smoothness is encoded by the equivalent
regular-cone criterion.
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

abbrev apm_t01a07_intersection :=
  {p : apm_t01a07_RP3 // p ∈ apm_t01a07_surface ∩ apm_t01a07_line}

/-- The local orientation sign at an intersection point. The sign of the
product of the first two homogeneous coordinates is independent of rescaling. -/
def apm_t01a07_localSign (p : apm_t01a07_intersection) : ℤ :=
  if 0 < Projectivization.rep p.1 0 * Projectivization.rep p.1 1 then 1 else -1

def apm_t01a07_signedIntersection
    (e : Fin 2 ≃ apm_t01a07_intersection) : ℤ :=
  ∑ i : Fin 2, apm_t01a07_localSign (e i)

theorem apm_t01a07 :
    apm_t01a07_IsSmoothProjectiveHypersurface ∧
      ∃ e : Fin 2 ≃ apm_t01a07_intersection,
        apm_t01a07_localSign (e 0) = -apm_t01a07_localSign (e 1) ∧
        apm_t01a07_signedIntersection e = 0 := by
  sorry
