import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.CoveringDegree
import ConstructionTargets.CoveringSubgroupCorrespondence
import ConstructionTargets.StandardSurfaceFiniteCover

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

/-- Adapter: an index-`k` subgroup `H` of `π₁(F, p)` is the fundamental group
of a connected `k`-sheeted cover of the standard genus-two surface. -/
theorem apm_t94J04_subgroup_standard_cover_adapter
    {F : Type} [TopologicalSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F] [CompactSpace F]
    (hF : apm_t94J04_isGenusTwoSurface F) (p : F) (k : ℕ)
    (H : Subgroup (FundamentalGroup F p)) (hH : H.index = k) :
    ∃ (E : Type) (_ : TopologicalSpace E)
      (q : E → ConstructionTargets.Surfaces.Surface true 2) (e : E),
      IsCoveringMap q ∧ PathConnectedSpace E ∧
      (∀ b, Nat.card {x : E // q x = b} = k) ∧
      Nonempty (FundamentalGroup E e ≃* H) := by
  sorry

/-- Adapter: a group isomorphic to `π₁` of a space homeomorphic to the standard
genus-`(k+1)` surface is isomorphic to its `π₁` at `surfacePoint`. -/
theorem apm_t94J04_cover_group_transport_adapter
    (k : ℕ) (H : Type*) [Group H]
    (E : Type*) [TopologicalSpace E] [PathConnectedSpace E] (e : E)
    (hE : Nonempty
      (E ≃ₜ ConstructionTargets.Surfaces.Surface true (k + 1)))
    (hpi : Nonempty (FundamentalGroup E e ≃* H)) :
    Nonempty
      (H ≃* FundamentalGroup
        (ConstructionTargets.Surfaces.Surface true (k + 1))
        (ConstructionTargets.StatementSurfaceModels.surfacePoint true (k + 1))) := by
  sorry

theorem apm_t94J04_finiteIndexSurfaceSubgroupClassification
    {F : Type} [TopologicalSpace F] [T2Space F] [CompactSpace F]
    [PathConnectedSpace F] [ChartedSpace apm_t94J04_E F]
    [IsManifold (𝓘(ℝ, apm_t94J04_E)) ∞ F]
    (hF : apm_t94J04_isGenusTwoSurface F)
    (p : F) (k : ℕ) (hk : 2 ≤ k)
    (H K : Subgroup (FundamentalGroup F p))
    (hH : H.index = k) (hK : K.index = k) :
    Nonempty (H ≃* K) := by
  obtain ⟨EH, topH, qH, eH, hqH, hcH, hfH, hpiH⟩ :=
    apm_t94J04_subgroup_standard_cover_adapter hF p k H hH
  obtain ⟨EK, topK, qK, eK, hqK, hcK, hfK, hpiK⟩ :=
    apm_t94J04_subgroup_standard_cover_adapter hF p k K hK
  letI : TopologicalSpace EH := topH
  letI : PathConnectedSpace EH := hcH
  letI : TopologicalSpace EK := topK
  letI : PathConnectedSpace EK := hcK
  have hk : 1 ≤ k := by omega
  obtain ⟨hsH⟩ :=
    ConstructionTargets.StandardSurfaceFiniteCover.connectedFiniteCover_homeomorph_standardSurface
      2 k (by omega) hk EH qH hqH hfH
  obtain ⟨hsK⟩ :=
    ConstructionTargets.StandardSurfaceFiniteCover.connectedFiniteCover_homeomorph_standardSurface
      2 k (by omega) hk EK qK hqK hfK
  have harith : k * (2 - 1) + 1 = k + 1 := by omega
  rw [harith] at hsH hsK
  obtain ⟨iH⟩ := apm_t94J04_cover_group_transport_adapter k H EH eH ⟨hsH⟩ hpiH
  obtain ⟨iK⟩ := apm_t94J04_cover_group_transport_adapter k K EK eK ⟨hsK⟩ hpiK
  exact ⟨iH.trans iK.symm⟩

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
