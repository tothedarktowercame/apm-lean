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

lemma apm_t94J04_subgroups_equiv_of_index_one
    {G : Type*} [Group G] (H K : Subgroup G)
    (hH : H.index = 1) (hK : K.index = 1) : Nonempty (H ≃* K) := by
  rw [Subgroup.index_eq_one] at hH hK
  subst H
  subst K
  exact ⟨MulEquiv.refl _⟩

theorem apm_t94j04
    {F : Type} [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F]
    [IsManifold (𝓘(ℝ, apm_t94J04_E)) ∞ F]
    (hF : apm_t94J04_hasOrientedGenusTwoHomology F)
    (p : F) (k : ℕ) (hk : 0 < k)
    (H K : Subgroup (FundamentalGroup F p))
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty (H ≃* K) := by
  /-
  Boundary (closer hop 1): the index-one edge case is now closed by
  `apm_t94J04_subgroups_equiv_of_index_one`.  For general positive `k`, the
  intended proof realizes each subgroup as the fundamental group of its
  connected `k`-sheeted covering surface, uses multiplicativity of Euler
  characteristic to compute genus `k+1`, and applies classification of closed
  orientable surfaces.

  Searches of `ConstructionTargets/`, `LEMMA-INDEX.md`, closed surface and
  covering artifacts, git history, and Mathlib's covering-space,
  fundamental-group, singular-homology, Euler-characteristic, surface,
  Schreier, and Nielsen--Schreier APIs found no subgroup--cover realization,
  finite-cover Euler-characteristic theorem, or surface-classification theorem
  for this concrete manifold.  `Subgroup.rank_le_index_mul_rank` and
  `subgroupIsFreeOfIsFree` concern free groups and do not apply to the
  one-relator genus-two surface group.  Moreover the frozen homology predicate
  must first be connected to an actual genus-two surface classification.
  Those topological bridges remain open.
  -/
  sorry
