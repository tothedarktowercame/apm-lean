import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t94J04

## Statement repairs

The index `k` is required to be positive.  Mathlib represents infinite index
by `Subgroup.index = 0`; without `0 < k`, the statement would incorrectly
claim that all infinite-index subgroups of a genus-two surface group are
isomorphic.  The informal solution also explicitly assumes `k ≥ 1`.

## Encoding questions

The group is the actual Mathlib fundamental group of a compact connected
smooth surface. Following `t00A02`, genus two and orientability are encoded by
the surface's characteristic integral homology groups: `H₀ = ℤ`, `H₁ = ℤ⁴`,
`H₂ = ℤ`, and vanishing higher homology. Subgroups, their index, and the
resulting group isomorphism are all native.
-/

open CategoryTheory
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t94J04_E := EuclideanSpace ℝ (Fin 2)

abbrev apm_t94J04_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- The integral homology of a closed orientable surface of genus two. -/
def apm_t94J04_hasOrientedGenusTwoHomology
    (F : Type) [TopologicalSpace F] : Prop :=
  Nonempty (apm_t94J04_H 0 F ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t94J04_H 1 F ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t94J04_H 2 F ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t94J04_H k F)

theorem apm_t94j04
    {F : Type} [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F]
    [IsManifold (𝓘(ℝ, apm_t94J04_E)) ∞ F]
    (hF : apm_t94J04_hasOrientedGenusTwoHomology F)
    (p : F) (k : ℕ) (hk : 0 < k)
    (H K : Subgroup (FundamentalGroup F p))
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty (H ≃* K) := by
  sorry
