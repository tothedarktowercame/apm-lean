import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.StandardSurfaceFiniteCover

open Set Topology ConstructionTargets.Surfaces

noncomputable section

abbrev apm_t91J05_Surface (g : ℕ) := Surface true g

def apm_t91J05_IsFiniteCover
    (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ p : X → apm_t91J05_Surface 3,
    IsCoveringMap p ∧ Function.Surjective p ∧
    ∀ s : apm_t91J05_Surface 3, (p ⁻¹' ({s} : Set _)).Finite

-- SEAT AREA
/-- The total space of a local homeomorphism onto a locally path-connected
space is locally path-connected. -/
theorem apm_t91J05_connected_finite_cover_classification_aux_locPath
    {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [LocPathConnectedSpace B] {p : X → B} (hp : IsLocalHomeomorph p) :
    LocPathConnectedSpace X := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x F hFo hxF
  have hF : F ∈ 𝓝 x := hFo.mem_nhds hxF
  obtain ⟨e, hxe, rfl⟩ := hp x
  have hV : e.source ∩ F ∈ 𝓝 x :=
    Filter.inter_mem (e.open_source.mem_nhds hxe) hF
  have hT : e.target ∩ e.symm ⁻¹' (e.source ∩ F) ∈ 𝓝 (e x) := by
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hxe)) ?_
    apply e.continuousAt_symm (e.map_source hxe)
    rwa [e.left_inv hxe]
  set N := pathComponentIn (e.target ∩ e.symm ⁻¹' (e.source ∩ F)) (e x)
  have hN : N ∈ 𝓝 (e x) := pathComponentIn_mem_nhds hT
  have hNsub : N ⊆ e.target ∩ e.symm ⁻¹' (e.source ∩ F) := pathComponentIn_subset
  have hxN : e x ∈ N := mem_pathComponentIn_self (mem_of_mem_nhds hT)
  have himg : IsPathConnected (e.symm '' N) :=
    (isPathConnected_pathComponentIn (mem_of_mem_nhds hT)).image'
      (e.continuousOn_symm.mono fun y hy => (hNsub hy).1)
  have hximg : x ∈ e.symm '' N := ⟨e x, hxN, e.left_inv hxe⟩
  have himgF : e.symm '' N ⊆ F := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hNsub hy).2.2
  have hsub : e.symm '' N ⊆ pathComponentIn F x :=
    himg.subset_pathComponentIn hximg himgF
  refine Filter.mem_of_superset ?_ hsub
  have hpre : e.source ∩ e ⁻¹' N ∈ 𝓝 x :=
    Filter.inter_mem (e.open_source.mem_nhds hxe)
      (e.continuousAt hxe |>.preimage_mem_nhds hN)
  refine Filter.mem_of_superset hpre ?_
  rintro y ⟨hys, hyN⟩
  exact ⟨e y, hyN, e.left_inv hys⟩

/-- Over a connected base, a covering map has a locally constant, hence
constant, fibre cardinality. -/
theorem apm_t91J05_connected_finite_cover_classification_aux_sheets
    {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] [PreconnectedSpace B]
    {p : X → B} (hp : IsCoveringMap p) (b₀ b : B) :
    Nat.card {e : X // p e = b} = Nat.card {e : X // p e = b₀} := by
  have hloc : IsLocallyConstant (fun b : B => Nat.card {e : X // p e = b}) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨_, U, hxU, hU, _, H, hH⟩ := hp x
    filter_upwards [hU.mem_nhds hxU] with y hy
    have key : ∀ z (hz : z ∈ U),
        Nat.card {e : X // p e = z} = Nat.card (p ⁻¹' {x}) := by
      intro z hz
      refine Nat.card_congr
        { toFun := fun e => (H ⟨e.1, by simp [mem_preimage, e.2, hz]⟩).2
          invFun := fun i => ⟨H.symm (⟨z, hz⟩, i), by
            have := hH (H.symm (⟨z, hz⟩, i))
            simp only [Homeomorph.apply_symm_apply] at this
            exact this.symm⟩
          left_inv := ?_
          right_inv := ?_ }
      · rintro ⟨e, he⟩
        apply Subtype.ext
        have h1 : (H ⟨e, by simp [mem_preimage, he, hz]⟩).1 = ⟨z, hz⟩ :=
          Subtype.ext ((hH _).trans he)
        change ((H.symm (⟨z, hz⟩, _) : p ⁻¹' U) : X) = e
        rw [← h1, Prod.mk.eta, Homeomorph.symm_apply_apply]
      · intro i
        simp
    rw [key y hy, key x hxU]
  exact hloc.apply_eq_of_preconnectedSpace b b₀

-- END SEAT AREA

/-- LIBRARY: recognition and Euler-characteristic multiplication for a
connected finite cover of the concrete genus-three polygon surface. -/
theorem apm_t91J05_connected_finite_cover_classification
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X]
    (hX : apm_t91J05_IsFiniteCover X) :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (X ≃ₜ apm_t91J05_Surface (2 * n + 1)) := by
  obtain ⟨p, hp, hsurj, hfin⟩ := hX
  haveI : LocPathConnectedSpace Disk := (convex_closedBall (0 : ℂ) 1).locPathConnectedSpace
  haveI : LocPathConnectedSpace (apm_t91J05_Surface 3) :=
    LocPathConnectedSpace.coinduced (fun x : Disk ↦ Quotient.mk _ x)
  haveI : LocPathConnectedSpace X :=
    apm_t91J05_connected_finite_cover_classification_aux_locPath hp.isLocalHomeomorph
  haveI : PathConnectedSpace X := PathConnectedSpace.of_locPathConnectedSpace
  haveI : ConnectedSpace (apm_t91J05_Surface 3) := hsurj.connectedSpace hp.continuous
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set b₀ := p x₀
  set n := Nat.card {e : X // p e = b₀}
  have hn : 0 < n := by
    haveI : Finite {e : X // p e = b₀} := (hfin b₀).to_subtype
    exact Nat.card_pos_iff.mpr ⟨⟨⟨x₀, rfl⟩⟩, inferInstance⟩
  have hsheets : ∀ b, Nat.card {e : X // p e = b} = n := fun b =>
    apm_t91J05_connected_finite_cover_classification_aux_sheets hp b₀ b
  obtain ⟨h⟩ :=
    ConstructionTargets.StandardSurfaceFiniteCover.connectedFiniteCover_homeomorph_standardSurface
      3 n (by norm_num) hn X p hp hsheets
  have harith : n * (3 - 1) + 1 = 2 * n + 1 := by omega
  rw [harith] at h
  exact ⟨n, hn, ⟨h⟩⟩

#print axioms apm_t91J05_connected_finite_cover_classification
