import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.CoveringSubgroupCorrespondence

/-!
# Blueprint for APM t00J06

The proof is split at the natural interface between the surface-group
calculation and the covering-subgroup correspondence.  Both library lemmas
can therefore be developed independently.
-/

open CategoryTheory Set
open scoped ContDiff Manifold
open ConstructionTargets.CoveringSubgroupCorrespondence

noncomputable section

abbrev apm_t00J06_Torus := Circle × Circle
abbrev apm_t00J06_E := EuclideanSpace ℝ (Fin 2)

abbrev apm_t00J06_H (k : ℕ) (S : Type) [TopologicalSpace S] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of S))

def apm_t00J06_hasGenusTwoHomology (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (apm_t00J06_H 0 S ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t00J06_H 1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t00J06_H 2 S ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t00J06_H k S)

/-- A fixed basepoint of the product-circle model of the torus. -/
def apm_t00J06_torusBase : apm_t00J06_Torus := (1, 1)

/-- The subgroup of the surface fundamental group carried by the map from
the torus. -/
def apm_t00J06_imageSubgroup
    {S : Type} [TopologicalSpace S]
    (f : C(apm_t00J06_Torus, S)) :
    Subgroup (FundamentalGroup S (f apm_t00J06_torusBase)) :=
  (FundamentalGroup.map f apm_t00J06_torusBase).range

/-- **LIBRARY (surface classification / finite-cover homology).**  The image
of the fundamental group of a torus in a closed orientable genus-two surface
has infinite index.  Mathlib encodes infinite subgroup index by `0`. -/
theorem apm_t00J06_torus_image_index_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S]
    (hS : apm_t00J06_hasGenusTwoHomology S)
    (f : C(apm_t00J06_Torus, S)) :
    (apm_t00J06_imageSubgroup f).index = 0 := by
  sorry

/- **LIBRARY (covering-subgroup correspondence).**  An infinite-index image
subgroup is realized by a connected cover, the original map lifts to that
cover, and cosets identify every fiber with an infinite set. -/
/-- Manifold charts supply the small simply connected coordinate balls needed
for semilocal simple connectivity. -/
theorem apm_t00J06_surface_semilocallySimplyConnected
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S] :
    SemilocallySimplyConnected S := by
  intro x
  let e := chartAt apm_t00J06_E x
  have hxsource : x ∈ e.source := mem_chart_source _ x
  have hxtarget : e x ∈ e.target := e.map_source hxsource
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) hxtarget
  let B : Set apm_t00J06_E := Metric.ball (e x) r
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

/-- The product-circle model is path-connected and locally path-connected. -/
theorem apm_t00J06_torus_path_and_locallyPathConnected :
    PathConnectedSpace apm_t00J06_Torus ∧
      LocPathConnectedSpace apm_t00J06_Torus := by
  letI : PathConnectedSpace Circle :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (E := ℂ) (by simp) 0 (by norm_num : (0 : ℝ) ≤ 1))
  letI : LocPathConnectedSpace Circle :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle
  letI : PathConnectedSpace (Circle × Circle) :=
    ⟨⟨(1, 1)⟩, fun x y =>
      ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1)
        (PathConnectedSpace.somePath x.2 y.2)⟩⟩
  letI : LocPathConnectedSpace (Circle × Circle) :=
    LocPathConnectedSpace.of_bases
      (fun x => (path_connected_basis x.1).prod_nhds (path_connected_basis x.2))
      (by
        intro x i hi
        rcases hi with ⟨⟨_, hU⟩, ⟨_, hV⟩⟩
        rw [isPathConnected_iff]
        refine ⟨hU.nonempty.prod hV.nonempty, ?_⟩
        intro a ha b hb
        let p := hU.joinedIn a.1 ha.1 b.1 hb.1
        let q := hV.joinedIn a.2 ha.2 b.2 hb.2
        exact ⟨Path.prod p.somePath q.somePath,
          fun t => ⟨p.somePath_mem t, q.somePath_mem t⟩⟩)
  exact ⟨inferInstance, inferInstance⟩

theorem apm_t00J06_connected_infinite_cover_of_image_index_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S]
    (f : C(apm_t00J06_Torus, S))
    (hindex : (apm_t00J06_imageSubgroup f).index = 0) :
    ∃ (X : Type*) (_ : TopologicalSpace X) (_ : ConnectedSpace X) (p : X → S),
      IsCoveringMap p ∧
      (∀ s : S, (p ⁻¹' ({s} : Set S)).Infinite) ∧
      ∃ lift : C(apm_t00J06_Torus, X), ∀ x, p (lift x) = f x := by
  letI : LocPathConnectedSpace S :=
    ChartedSpace.locPathConnectedSpace apm_t00J06_E S
  let H := apm_t00J06_imageSubgroup f
  obtain ⟨X, topX, p, e, hp, hX, hpe, hrange, hpi, hcoset⟩ :=
    exists_connected_subgroup_cover_of_small.{0, u_1}
      (apm_t00J06_surface_semilocallySimplyConnected S)
      (f apm_t00J06_torusBase) H
  letI : TopologicalSpace X := topX
  letI : ConnectedSpace X := PathConnectedSpace.connectedSpace
  have hinfinite : ∀ s : S, (p ⁻¹' ({s} : Set S)).Infinite :=
    every_fiber_infinite_of_coset_equiv hp (f apm_t00J06_torusBase) H hindex hcoset
  have hle : (FundamentalGroup.map f apm_t00J06_torusBase).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpe).range := by
    rw [hrange]
    exact le_rfl
  letI : PathConnectedSpace apm_t00J06_Torus :=
    apm_t00J06_torus_path_and_locallyPathConnected.1
  letI : LocPathConnectedSpace apm_t00J06_Torus :=
    apm_t00J06_torus_path_and_locallyPathConnected.2
  obtain ⟨lift, hlift⟩ :=
    exists_continuousMap_lift_of_range_le hp f apm_t00J06_torusBase e hpe hle
  exact ⟨X, topX, inferInstance, p, hp, hinfinite, lift, hlift⟩

/-- Every map from the torus to the closed oriented genus-two surface lifts to
a connected infinite-sheeted covering. -/
theorem apm_t00j06
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S]
    (hS : apm_t00J06_hasGenusTwoHomology S)
    (f : C(apm_t00J06_Torus, S)) :
    ∃ (X : Type*) (_ : TopologicalSpace X) (_ : ConnectedSpace X) (p : X → S),
      IsCoveringMap p ∧
      (∀ s : S, (p ⁻¹' ({s} : Set S)).Infinite) ∧
      ∃ lift : C(apm_t00J06_Torus, X), ∀ x, p (lift x) = f x := by
  apply apm_t00J06_connected_infinite_cover_of_image_index_zero f
  exact apm_t00J06_torus_image_index_zero hS f

#print axioms apm_t00j06
