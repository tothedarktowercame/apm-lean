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
lemma apm_t94J04_subgroup_standard_cover_adapter_aux_slsc
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace apm_t94J04_E S] :
    ConstructionTargets.CoveringSubgroupCorrespondence.SemilocallySimplyConnected S := by
  intro x
  let e := chartAt apm_t94J04_E x
  have hxsource : x ∈ e.source := mem_chart_source _ x
  have hxtarget : e x ∈ e.target := e.map_source hxsource
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) hxtarget
  let B : Set apm_t94J04_E := Metric.ball (e x) r
  let U : Set S := e.symm '' B
  have hBsub : B ⊆ e.symm.source := by
    simpa [B] using hrsub
  have hU_nhds : U ∈ nhds x := by
    have hB_nhds : B ∈ nhds (e x) := Metric.ball_mem_nhds _ hr
    have him := e.symm.image_mem_nhds hxtarget hB_nhds
    simpa [U, e, e.left_inv hxsource] using him
  refine ⟨U, hU_nhds, fun γ hγ ↦ ?_⟩
  let h : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hBsub rfl
  letI : ContractibleSpace B :=
    (convex_ball (e x) r).contractibleSpace ⟨e x, by simpa [B] using hr⟩
  letI : ContractibleSpace U := h.symm.contractibleSpace
  letI : SimplyConnectedSpace U := inferInstance
  have hxU : x ∈ U := hγ ⟨0, Path.source γ⟩
  let xU : U := ⟨x, hxU⟩
  let γU : Path xU xU := {
    toFun := fun t ↦ (⟨γ t, hγ ⟨t, rfl⟩⟩ : U)
    continuous_toFun := (Path.continuous γ).subtype_mk _
    source' := Subtype.ext (Path.source γ)
    target' := Subtype.ext (Path.target γ)
  }
  have hhom : γU.Homotopic (Path.refl xU) :=
    SimplyConnectedSpace.paths_homotopic _ _
  let inc : C(U, S) := ⟨Subtype.val, continuous_subtype_val⟩
  have hmapped := hhom.map inc
  apply Path.Homotopic.Quotient.eq.mpr
  simpa [γU] using hmapped

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
  letI : LocPathConnectedSpace F :=
    ChartedSpace.locPathConnectedSpace apm_t94J04_E F
  obtain ⟨f⟩ := hF
  obtain ⟨E, topE, r, e, hr, hE, hre, hcard, hpi⟩ :=
    ConstructionTargets.CoveringSubgroupCorrespondence.connectedCover
      (apm_t94J04_subgroup_standard_cover_adapter_aux_slsc F) p H
  let q : E → ConstructionTargets.Surfaces.Surface true 2 := f ∘ r
  refine ⟨E, topE, q, e, hr.homeomorph_comp f, hE, ?_, hpi⟩
  intro b
  obtain ⟨efib⟩ :=
    ConstructionTargets.CoveringSubgroupCorrespondence.covering_fiber_equiv
      hr p (f.symm b)
  have hy : Nat.card (r ⁻¹' ({f.symm b} : Set F)) = k := by
    calc
      Nat.card (r ⁻¹' ({f.symm b} : Set F)) =
          Nat.card (r ⁻¹' ({p} : Set F)) := Nat.card_congr efib.symm
      _ = H.index := hcard
      _ = k := hH
  let eqv : {x : E // q x = b} ≃ (r ⁻¹' ({f.symm b} : Set F)) := {
    toFun := fun x ↦ ⟨x.1, by
      change r x.1 ∈ ({f.symm b} : Set F)
      simp only [Set.mem_singleton_iff]
      apply f.injective
      simpa [q] using x.2⟩
    invFun := fun x ↦ ⟨x.1, by
      change f (r x.1) = b
      have hxmem : r x.1 ∈ ({f.symm b} : Set F) := x.2
      have hx : r x.1 = f.symm b := Set.mem_singleton_iff.mp hxmem
      simpa [hx]⟩
    left_inv x := Subtype.ext rfl
    right_inv x := Subtype.ext rfl }
  exact (Nat.card_congr eqv).trans hy

/-- Adapter: a group isomorphic to `π₁` of a space homeomorphic to the standard
genus-`(k+1)` surface is isomorphic to its `π₁` at `surfacePoint`. -/
noncomputable def apm_t94J04_cover_group_transport_adapter_aux_equiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (f x) where
  toFun := FundamentalGroup.map ⟨f, f.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨f.symm, f.symm.continuous⟩
    (f.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map f.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact f.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact f.apply_symm_apply (p t)
  map_mul' := map_mul _

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
  obtain ⟨f⟩ := hE
  obtain ⟨i⟩ := hpi
  letI : PathConnectedSpace
      (ConstructionTargets.Surfaces.Surface true (k + 1)) :=
    f.surjective.pathConnectedSpace f.continuous
  exact ⟨i.symm |>.trans
    (apm_t94J04_cover_group_transport_adapter_aux_equiv f e) |>.trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (f e)
      (ConstructionTargets.StatementSurfaceModels.surfacePoint true (k + 1)))⟩

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
