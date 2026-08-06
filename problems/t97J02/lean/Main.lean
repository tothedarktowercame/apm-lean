import Mathlib

/-!
# APM t97J02

## Statement repairs

None.

## Encoding questions

Mathlib has neither connected sums of surfaces nor canonical closed-surface
types indexed by orientability and genus. The exact base `N₄` and the
standard classified surfaces are therefore isolated as typed opaque spaces;
they are not replaced by Euler-characteristic numbers. Coverings are genuine
Mathlib `IsCoveringMap`s with exact fiber cardinality, and the exhaustive
clauses quantify over every compact connected smooth `2`-manifold covering
the base.
-/

open Set
open scoped Manifold ContDiff

noncomputable section

abbrev apm_t97J02_E2 := EuclideanSpace ℝ (Fin 2)

/-- The connected sum of four real projective planes, `N₄`. -/
opaque apm_t97J02_X : Type

opaque apm_t97J02_X_topology : TopologicalSpace apm_t97J02_X

noncomputable instance : TopologicalSpace apm_t97J02_X :=
  apm_t97J02_X_topology

/-- The standard closed surface of the given orientability and genus. -/
opaque apm_t97J02_Surface (orientable : Bool) (genus : ℕ) : Type

opaque apm_t97J02_Surface_topology (orientable : Bool) (genus : ℕ) :
    TopologicalSpace (apm_t97J02_Surface orientable genus)

noncomputable instance (orientable : Bool) (genus : ℕ) :
    TopologicalSpace (apm_t97J02_Surface orientable genus) :=
  apm_t97J02_Surface_topology orientable genus

/-- An exact `n`-sheeted covering of `N₄`. -/
def apm_t97J02_IsNfoldCover
    {E : Type*} [TopologicalSpace E] (n : ℕ) (p : E → apm_t97J02_X) : Prop :=
  IsCoveringMap p ∧
    ∀ x : apm_t97J02_X, Nat.card {e : E // p e = x} = n

/-- A covering carried by one of the canonical classified surfaces. -/
structure apm_t97J02_CoverWitness (orientable : Bool) (genus n : ℕ) where
  p : apm_t97J02_Surface orientable genus → apm_t97J02_X
  covering : apm_t97J02_IsNfoldCover n p

theorem apm_t97j02 :
    Nonempty (apm_t97J02_CoverWitness false 12 5) ∧
    (∀ (E : Type*) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ∞ E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 5 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface false 12)) ∧
    Nonempty (apm_t97J02_CoverWitness true 7 6) ∧
    Nonempty (apm_t97J02_CoverWitness false 14 6) ∧
    ∀ (E : Type*) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ∞ E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 6 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface true 7) ∨
        Nonempty (E ≃ₜ apm_t97J02_Surface false 14) := by
  sorry
