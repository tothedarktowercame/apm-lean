import Mathlib
import ConstructionTargets.Surfaces

/-!
# APM t91J05 — finite covers of the genus-three orientable surface

Closed orientable surfaces are the explicit polygon quotients supplied by
`ConstructionTargets.Surfaces`.  Covering maps, finite fibers, connectedness,
and classification up to homeomorphism remain native topological notions.

## Statement repairs

The classification is stated for connected covering spaces.  Without
connectedness, a finite cover may be a finite disjoint union of the classified
connected covers, so “exactly the odd-genus surfaces” would be incomplete.

The former opaque carrier and topology are replaced by the concrete polygon
presentation `ConstructionTargets.Surfaces.Surface true g`.

## Encoding questions

None.
-/

open Set ConstructionTargets.Surfaces

noncomputable section

abbrev apm_t91J05_Surface (g : ℕ) := Surface true g

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
