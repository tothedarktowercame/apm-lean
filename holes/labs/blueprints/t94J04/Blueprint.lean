import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.CoveringDegree

open CategoryTheory
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t94J04_E := EuclideanSpace ℝ (Fin 2)

abbrev apm_t94J04_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- `F` is homeomorphic to the standard orientable genus-two polygon model. -/
def apm_t94J04_isGenusTwoSurface
    (F : Type) [TopologicalSpace F] : Prop :=
  Nonempty (F ≃ₜ ConstructionTargets.Surfaces.Surface true 2)

/-- Index-one subgroups are both the top subgroup. -/
theorem apm_t94J04_subgroups_equiv_of_index_one
    {G : Type*} [Group G] (H K : Subgroup G)
    (hH : H.index = 1) (hK : K.index = 1) : Nonempty (H ≃* K) := by
  rw [Subgroup.index_eq_one] at hH hK
  subst H
  subst K
  exact ⟨MulEquiv.refl _⟩

/-- The Euler-characteristic arithmetic for a `k`-sheeted cover of a
genus-two surface. -/
theorem apm_t94J04_eulerChar_cover_arithmetic (k : ℕ) :
    (2 : ℤ) - 2 * ((k : ℤ) + 1) = (k : ℤ) * (2 - 2 * 2) := by
  ring

/-- **LIBRARY.** Finite-index subgroups of the fundamental group of the
standard genus-two surface are determined, up to group isomorphism, by their
positive index. -/
theorem apm_t94J04_finiteIndexSurfaceSubgroupClassification
    {F : Type} [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F]
    [IsManifold (𝓘(ℝ, apm_t94J04_E)) ∞ F]
    (hF : apm_t94J04_isGenusTwoSurface F)
    (p : F) (k : ℕ) (hk : 2 ≤ k)
    (H K : Subgroup (FundamentalGroup F p))
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty (H ≃* K) := by
  sorry

theorem apm_t94j04
    {F : Type} [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F]
    [IsManifold (𝓘(ℝ, apm_t94J04_E)) ∞ F]
    (hF : apm_t94J04_isGenusTwoSurface F)
    (p : F) (k : ℕ) (hk : 0 < k)
    (H K : Subgroup (FundamentalGroup F p))
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty (H ≃* K) := by
  by_cases hk1 : k = 1
  · apply apm_t94J04_subgroups_equiv_of_index_one H K
    · simpa [hk1] using hH
    · simpa [hk1] using hK
  · apply apm_t94J04_finiteIndexSurfaceSubgroupClassification hF p k (by omega) H K hH hK

#print axioms apm_t94j04
