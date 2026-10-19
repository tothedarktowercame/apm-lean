import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.CoveringDegree
import ConstructionTargets.CoveringMonodromyCosets
import ConstructionTargets.SuppliedCoverAlgebra
import ConstructionTargets.CoveringSubgroupCorrespondence

/-! # Blueprint for t96A01: finite-index subgroups of a genus-four surface group -/

open ConstructionTargets.StatementSurfaceModels ConstructionTargets.Surfaces
open ConstructionTargets.CoveringSubgroupCorrespondence

noncomputable section

/-! ## Definitions shared by the independent lemma seats -/

/-- The canonical interior basepoint of the standard orientable polygon surface. -/
abbrev T96A01SurfaceBase (g : ℕ) : Surface true g :=
  surfacePoint true g

/-! ## Independent library interfaces -/

/-- **LIBRARY (polygon-surface fundamental group).**  The standard orientable
genus-`g` polygon quotient has the usual one-relator surface group. -/
theorem t96A01_orientableSurface_fundamentalGroup (g : ℕ) :
    Nonempty
      (FundamentalGroup (Surface true g) (T96A01SurfaceBase g) ≃*
        OrientableSurfaceGroup g) := by
  sorry

/-- Finite index rules out Mathlib's `index = 0` sentinel. -/
theorem t96A01_index_pos
    {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (n : ℕ) (hindex : H.index = n) :
    0 < n := by
  rw [← hindex]
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

/- **LIBRARY (covering-subgroup correspondence).**  A finite-index subgroup
is realized as the fundamental group of a connected cover whose fibre has the
prescribed cardinality. -/
/-- Surface charts give semilocally simply connected neighbourhoods.  No
`IsManifold` regularity is needed: this is a purely topological chart fact. -/
theorem t96A01_surface_semilocallySimplyConnected
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] :
    SemilocallySimplyConnected S := by
  intro x
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hxsource : x ∈ e.source := mem_chart_source _ x
  have hxtarget : e x ∈ e.target := e.map_source hxsource
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) hxtarget
  let B : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball (e x) r
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

/-- A compact surface is covered by finitely many chart sources, so it is the
image of a type in `Type`; this lets the cover be built in `Type` although `S`
lives in an arbitrary universe. -/
-- BEGIN SEAT AREA
theorem t96A01_surface_small
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [CompactSpace S] :
    Small.{0} S := by
  classical
  let U : S → Set S := fun x ↦ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U
    (fun x ↦ (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  have hchoose : ∀ x : S, ∃ i : S, i ∈ t ∧ x ∈ U i := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hit, hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hit, hx⟩
  let idx : S → S := fun x ↦ (hchoose x).choose
  have hidx_mem (x : S) : idx x ∈ t := (hchoose x).choose_spec.1
  have hxsource (x : S) : x ∈ U (idx x) := (hchoose x).choose_spec.2
  let f : S → (Shrink.{0} ↥t × EuclideanSpace ℝ (Fin 2)) := fun x ↦
    ((equivShrink.{0} ↥t) ⟨idx x, hidx_mem x⟩,
      chartAt (EuclideanSpace ℝ (Fin 2)) (idx x) x)
  apply small_of_injective (f := f)
  intro x y hxy
  have hidx_sub : (⟨idx x, hidx_mem x⟩ : ↥t) = ⟨idx y, hidx_mem y⟩ := by
    apply (equivShrink.{0} ↥t).injective
    exact congr_arg Prod.fst hxy
  have hidx : idx x = idx y := congr_arg Subtype.val hidx_sub
  have hchart : chartAt (EuclideanSpace ℝ (Fin 2)) (idx x) x =
      chartAt (EuclideanSpace ℝ (Fin 2)) (idx x) y := by
    have := congr_arg Prod.snd hxy
    simpa [f, hidx] using this
  exact (chartAt (EuclideanSpace ℝ (Fin 2)) (idx x)).injOn
    (hxsource x) (hidx ▸ hxsource y) hchart
-- END SEAT AREA

theorem t96A01_finiteIndexSubgroup_connectedCover
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (s : S)
    (n : ℕ) (hn : 0 < n) (H : Subgroup (FundamentalGroup S s))
    [H.FiniteIndex] (hindex : H.index = n) :
    ∃ (E : Type) (_ : TopologicalSpace E) (p : E → S) (e : E),
      IsCoveringMap p ∧ PathConnectedSpace E ∧ p e = s ∧
      Nat.card (p ⁻¹' {s}) = n ∧
      Nonempty (FundamentalGroup E e ≃* H) := by
  letI : LocPathConnectedSpace S :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
  letI : PathConnectedSpace S := PathConnectedSpace.of_locPathConnectedSpace
  haveI : Small.{0} S := t96A01_surface_small S
  obtain ⟨E, topE, p, e, hp, hE, hpe, hcard, hpi⟩ :=
    connectedCover (t96A01_surface_semilocallySimplyConnected S) s H
  exact ⟨E, topE, p, e, hp, hE, hpe, hcard.trans hindex, hpi⟩

/-- **LIBRARY (finite-cover Euler characteristic and surface recognition).**
A connected `n`-sheeted cover of a genus-four surface has genus `3*n+1`.
The conclusion includes the harmless basepoint transport needed downstream. -/
theorem t96A01_connectedFiniteCover_surfaceFundamentalGroup
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (hgenus : Nonempty (S ≃ₜ Surface true 4)) (s : S)
    (n : ℕ) (hn : 0 < n)
    (E : Type*) [TopologicalSpace E] [PathConnectedSpace E]
    (p : E → S) (e : E) (hp : IsCoveringMap p) (hpe : p e = s)
    (hsheets : Nat.card (p ⁻¹' {s}) = n) :
    Nonempty
      (FundamentalGroup E e ≃*
        FundamentalGroup (Surface true (3 * n + 1))
          (T96A01SurfaceBase (3 * n + 1))) := by
  sorry

theorem apm_t96a01
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (hgenus : Nonempty (S ≃ₜ Surface true 4)) (s : S)
    (n : ℕ) (H : Subgroup (FundamentalGroup S s))
    [H.FiniteIndex] (hindex : H.index = n) :
    Nonempty (H ≃* OrientableSurfaceGroup (3 * n + 1)) := by
  have hn : 0 < n := t96A01_index_pos H n hindex
  obtain ⟨E, topE, p, e, hp, hE, hpe, hsheets, hsubgroup⟩ :=
    t96A01_finiteIndexSubgroup_connectedCover s n hn H hindex
  letI : TopologicalSpace E := topE
  letI : PathConnectedSpace E := hE
  obtain ⟨hsurface⟩ :=
    t96A01_connectedFiniteCover_surfaceFundamentalGroup
      hgenus s n hn E p e hp hpe hsheets
  obtain ⟨hsubgroup⟩ := hsubgroup
  obtain ⟨hpi₁⟩ := t96A01_orientableSurface_fundamentalGroup (3 * n + 1)
  exact ⟨hsubgroup.symm.trans (hsurface.trans hpi₁)⟩

#print axioms apm_t96a01
