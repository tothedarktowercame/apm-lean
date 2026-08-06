import Mathlib

/-!
# APM t91J05

## Statement repairs

The classification is stated for connected covering spaces, as in the main
claim and proof of the supplied informal solution. Without connectedness, a
finite covering space may be any finite disjoint union of the classified
connected covers, so “exactly the odd-genus surfaces” would be incomplete.

## Encoding questions

Mathlib has no packaged connected-sum construction or classification object
for closed orientable surfaces. The genuine genus-`g` surface is therefore an
opaque typed space. Covering maps, finite fibers, connectedness, and the
classification homeomorphism are all native topological notions.
-/

open Set

/-- A closed connected orientable surface of genus `g`. -/
opaque apm_t91J05_Surface (g : ℕ) : Type

opaque apm_t91J05_surfaceTopology (g : ℕ) :
    TopologicalSpace (apm_t91J05_Surface g)

noncomputable instance (g : ℕ) :
    TopologicalSpace (apm_t91J05_Surface g) :=
  apm_t91J05_surfaceTopology g

/-- A space is a finite-sheeted covering space of the genus-three surface. -/
def apm_t91J05_IsFiniteCover
    (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ p : X → apm_t91J05_Surface 3,
    IsCoveringMap p ∧ Function.Surjective p ∧
    ∀ s : apm_t91J05_Surface 3, (p ⁻¹' ({s} : Set _)).Finite

theorem apm_t91j05
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] :
    apm_t91J05_IsFiniteCover X ↔
      ∃ n : ℕ, 0 < n ∧
        Nonempty (X ≃ₜ apm_t91J05_Surface (2 * n + 1)) := by
  sorry
