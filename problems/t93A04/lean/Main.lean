import Mathlib

/-! # APM t93A04: a line with smooth inverse image

## Statement repairs

None.

## Encoding question

Mathlib does not supply Sard's theorem and the regular-value theorem for an
arbitrary bundled smooth manifold.  The domain manifold and smooth-submanifold
predicate are retained as typed placeholders.  The target `ℝ³`, straight lines,
the map, and its set-theoretic inverse image are encoded directly.
-/

open Set

abbrev t93A04Point := EuclideanSpace ℝ (Fin 3)

def T93A04SmoothManifold : Type := by sorry
def T93A04Carrier (M : T93A04SmoothManifold) : Type := by sorry
def IsT93A04SmoothMap (M : T93A04SmoothManifold)
    (f : T93A04Carrier M → t93A04Point) : Prop := by sorry
def IsT93A04SmoothSubmanifold (M : T93A04SmoothManifold)
    (S : Set (T93A04Carrier M)) : Prop := by sorry

def IsT93A04StraightLine (ℓ : Set t93A04Point) : Prop :=
  ∃ (p v : t93A04Point), v ≠ 0 ∧ ℓ = {x | ∃ t : ℝ, x = p + t • v}

theorem apm_t93a04 :
    ∀ (M : T93A04SmoothManifold) (f : T93A04Carrier M → t93A04Point),
      IsT93A04SmoothMap M f →
      ∃ ℓ : Set t93A04Point,
        IsT93A04StraightLine ℓ ∧ IsT93A04SmoothSubmanifold M (f ⁻¹' ℓ) := by
  sorry
