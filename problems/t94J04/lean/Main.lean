import Mathlib

/-!
# APM t94J04

## Statement repairs

The index `k` is required to be positive.  Mathlib represents infinite index
by `Subgroup.index = 0`; without `0 < k`, the statement would incorrectly
claim that all infinite-index subgroups of a genus-two surface group are
isomorphic.  The informal solution also explicitly assumes `k ≥ 1`.

## Encoding questions

The group is the actual Mathlib fundamental group of a compact connected
smooth surface.  Mathlib has no packaged genus invariant for smooth surfaces,
so “closed orientable surface of genus two” is isolated as a typed predicate.
Subgroups, their index, and the resulting group isomorphism are all native.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t94J04_E := EuclideanSpace ℝ (Fin 2)

/-- The assertion that a compact smooth surface is oriented and has genus two. -/
opaque apm_t94J04_IsOrientedGenusTwoSurface
    (F : Type*) [TopologicalSpace F] [ChartedSpace apm_t94J04_E F] : Prop

theorem apm_t94j04
    {F : Type*} [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F]
    [IsManifold (𝓘(ℝ, apm_t94J04_E)) ∞ F]
    (hF : apm_t94J04_IsOrientedGenusTwoSurface F)
    (p : F) (k : ℕ) (hk : 0 < k)
    (H K : Subgroup (FundamentalGroup F p))
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty (H ≃* K) := by
  sorry
