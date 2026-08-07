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

lemma apm_t01a07_localSign_eq_one_or_neg_one
    (p : apm_t01a07_intersection) :
    apm_t01a07_localSign p = 1 ∨ apm_t01a07_localSign p = -1 := by
  unfold apm_t01a07_localSign
  split_ifs <;> simp

lemma apm_t01a07_signedIntersection_eq_zero_of_opposite
    (e : Fin 2 ≃ apm_t01a07_intersection)
    (h : apm_t01a07_localSign (e 0) = -apm_t01a07_localSign (e 1)) :
    apm_t01a07_signedIntersection e = 0 := by
  rw [apm_t01a07_signedIntersection, Fin.sum_univ_two, h]
  omega

theorem apm_t01a07 :
    apm_t01a07_IsSmoothProjectiveHypersurface ∧
      ∃ e : Fin 2 ≃ apm_t01a07_intersection,
        apm_t01a07_localSign (e 0) = -apm_t01a07_localSign (e 1) ∧
        apm_t01a07_signedIntersection e = 0 := by
  /-
  CLOSER HOP 1 boundary. The final signed-sum calculation is now isolated and
  proved as `apm_t01a07_signedIntersection_eq_zero_of_opposite`; the range of
  every local sign is recorded by `apm_t01a07_localSign_eq_one_or_neg_one`.

  The smoothness conjunct can be proved by explicitly differentiating the
  quartic and observing that its four partial derivatives vanish only at the
  zero vector. Mathlib has the scalar `fderiv` rules needed for this, but no
  packaged coordinate formula for this `Fin 4 → ℝ` polynomial; assembling the
  continuous-linear derivative and extracting its four coordinate values
  remains local work.

  The harder remaining bridge is classifying the projective intersection.
  From the line equations the quartic equation becomes `x₀⁴ = x₁⁴`, hence
  `x₀ = x₁` or `x₀ = -x₁`, and nonzeroness excludes both coordinates being
  zero. One must then turn these two homogeneous alternatives into an actual
  equivalence `Fin 2 ≃ apm_t01a07_intersection`. Mathlib's projectivization API
  exposes chosen representatives, but searches found no extensionality lemma
  directly converting proportional representatives to equality in the form
  needed here, nor a finite-cardinality theorem for such a projective zero
  locus. Searches covered `LEMMA-INDEX.md`, every `ConstructionTargets/`
  module, projective-algebraic siblings (`t02A06`, `t94A08`, `t00J03`), the
  Projectivization source, polynomial/fderiv APIs, and git history. No closed
  artifact packages this classification.
  -/
  sorry
