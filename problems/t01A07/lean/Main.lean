import Mathlib

/-!
# APM t01A07

## Statement repairs

Mathlib's projectivization currently has no tangent-orientation or oriented
intersection API from which the integer local signs can be derived.  Following
the reviewer's permitted repair, part (b) is stated as the orientation-free
mod-2 intersection number.  This is a declared weakening of the source's
integer-valued oriented intersection request.

## Encoding questions

The projective space, quartic, line, and their intersection subtype are encoded
concretely; smoothness is encoded by the equivalent regular-cone criterion.
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

/-- Equality of fourth powers over `ℝ` has exactly the two expected signs. -/
lemma apm_t01a07_fourth_pow_eq_iff (x y : ℝ) :
    x ^ 4 = y ^ 4 ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    have hs : x ^ 2 = y ^ 2 := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hs
  · rintro (rfl | rfl) <;> ring

/-- The projectivization API turns a scalar relation between the chosen
representatives into equality of projective points. -/
lemma apm_t01a07_eq_of_smul_rep_eq
    (p q : apm_t01a07_RP3) (a : ℝ)
    (h : a • Projectivization.rep q = Projectivization.rep p) : p = q := by
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
  exact (Projectivization.mk_eq_mk_iff' ℝ _ _
    (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q)).2 ⟨a, h⟩

theorem apm_t01a07 :
    apm_t01a07_IsSmoothProjectiveHypersurface ∧
      Nonempty (Fin 2 ≃ apm_t01a07_intersection) ∧
      Nat.card apm_t01a07_intersection = 2 ∧
      Nat.card apm_t01a07_intersection % 2 = 0 := by
  sorry
