import ConstructionTargets.CircleHomology

noncomputable section

namespace ConstructionTargets.SurfaceSchoenflies

theorem embeddedCircle_isClosed_range
    {M : Type} [TopologicalSpace M] [T2Space M]
    (j : C(Circle, M)) (hj : Topology.IsEmbedding j) :
    IsClosed (Set.range j) := by
  exact (isCompact_range j.continuous).isClosed

def embeddedCircleHomeomorphRange
    {M : Type} [TopologicalSpace M]
    (j : C(Circle, M)) (hj : Topology.IsEmbedding j) :
    Circle ≃ₜ Set.range j :=
  hj.toHomeomorph

theorem embeddedCircle_closedRange_and_homeomorph
    {M : Type} [TopologicalSpace M] [T2Space M]
    (j : C(Circle, M)) (hj : Topology.IsEmbedding j) :
    IsClosed (Set.range j) ∧ Nonempty (Circle ≃ₜ Set.range j) := by
  exact ⟨embeddedCircle_isClosed_range j hj,
    ⟨embeddedCircleHomeomorphRange j hj⟩⟩

abbrev EmbeddedCircleFiniteOpenSubcover
    {M : Type} [TopologicalSpace M] (j : C(Circle, M)) : Prop :=
  ∀ {ι : Type} (U : ι → Set M), (∀ i, IsOpen (U i)) →
    Set.range j ⊆ ⋃ i, U i → ∃ s : Finset ι, Set.range j ⊆ ⋃ i ∈ s, U i

theorem embeddedCircle_finite_open_subcover
    {M : Type} [TopologicalSpace M] (j : C(Circle, M)) :
    EmbeddedCircleFiniteOpenSubcover j := by
  intro ι U hU hcover
  exact (isCompact_range j.continuous).elim_finite_subcover U hU hcover

structure EmbeddedCircleFlatNeighborhood
    {M : Type} [TopologicalSpace M] (j : C(Circle, M)) (z : Circle) where
  V : Set Circle
  U : Set M
  open_V : IsOpen V
  open_U : IsOpen U
  mem_source : z ∈ V
  mem_target : j z ∈ U
  productChart : U ≃ₜ (V × Set.Ioo (-1 : ℝ) 1)
  flatten : ∀ w (hw : w ∈ V), ∃ hwU : j w ∈ U,
    productChart ⟨j w, hwU⟩ = (⟨w, hw⟩, ⟨0, by norm_num⟩)

abbrev EmbeddedCircleLocallyFlat
    {M : Type} [TopologicalSpace M] (j : C(Circle, M)) : Prop :=
  ∀ z, Nonempty (EmbeddedCircleFlatNeighborhood j z)

def chosenFlatNeighborhood
    {M : Type} [TopologicalSpace M] {j : C(Circle, M)}
    (hflat : EmbeddedCircleLocallyFlat j) (z : Circle) :
    EmbeddedCircleFlatNeighborhood j z :=
  Classical.choice (hflat z)

theorem embeddedCircle_finite_flat_subcover
    {M : Type} [TopologicalSpace M] (j : C(Circle, M))
    (hflat : EmbeddedCircleLocallyFlat j) :
    ∃ s : Finset Circle, Set.range j ⊆
      ⋃ z ∈ s, (chosenFlatNeighborhood hflat z).U := by
  apply embeddedCircle_finite_open_subcover j
  · exact fun z => (chosenFlatNeighborhood hflat z).open_U
  · rintro _ ⟨z, rfl⟩
    exact Set.mem_iUnion.2 ⟨z, (chosenFlatNeighborhood hflat z).mem_target⟩

def EmbeddedCircleFlatNeighborhood.comapHomeomorph
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (j : C(Circle, M)) (z : Circle)
    (h : EmbeddedCircleFlatNeighborhood
      ((⟨e, e.continuous⟩ : C(M, N)).comp j) z) :
    EmbeddedCircleFlatNeighborhood j z where
  V := h.V
  U := e ⁻¹' h.U
  open_V := h.open_V
  open_U := e.isOpen_preimage.mpr h.open_U
  mem_source := h.mem_source
  mem_target := h.mem_target
  productChart :=
    (e.subtype (fun _ => Iff.rfl)).trans h.productChart
  flatten := by
    intro w hw
    obtain ⟨hwU, heq⟩ := h.flatten w hw
    exact ⟨hwU, heq⟩

theorem embeddedCircleLocallyFlat_homeomorph_iff
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (j : C(Circle, M)) :
    EmbeddedCircleLocallyFlat ((⟨e, e.continuous⟩ : C(M, N)).comp j) ↔
      EmbeddedCircleLocallyFlat j := by
  constructor
  · intro h z
    exact ⟨EmbeddedCircleFlatNeighborhood.comapHomeomorph e j z
      (Classical.choice (h z))⟩
  · intro h z
    let k : C(Circle, N) := (⟨e, e.continuous⟩ : C(M, N)).comp j
    have hk : (⟨e.symm, e.symm.continuous⟩ : C(N, M)).comp k = j := by
      ext
      simp [k]
    have hj' : EmbeddedCircleFlatNeighborhood
        ((⟨e.symm, e.symm.continuous⟩ : C(N, M)).comp k) z := by
      rw [hk]
      exact Classical.choice (h z)
    exact ⟨EmbeddedCircleFlatNeighborhood.comapHomeomorph e.symm k z hj'⟩

def EmbeddedCircleFlatNeighborhood.reparam
    {M : Type} [TopologicalSpace M] (j : C(Circle, M))
    (e : Circle ≃ₜ Circle) (z : Circle)
    (n : EmbeddedCircleFlatNeighborhood j (e z)) :
    EmbeddedCircleFlatNeighborhood
      (j.comp (⟨e, e.continuous⟩ : C(Circle, Circle))) z where
  V := e ⁻¹' n.V
  U := n.U
  open_V := e.isOpen_preimage.mpr n.open_V
  open_U := n.open_U
  mem_source := n.mem_source
  mem_target := n.mem_target
  productChart := n.productChart.trans
    (Homeomorph.prodCongr (e.subtype (fun _ => Iff.rfl))
      (Homeomorph.refl _)).symm
  flatten := by
    intro w hw
    obtain ⟨hwU, heq⟩ := n.flatten (e w) hw
    refine ⟨hwU, ?_⟩
    change (Homeomorph.prodCongr (e.subtype (fun _ => Iff.rfl))
      (Homeomorph.refl _)).symm
        (n.productChart ⟨j (e w), hwU⟩) = _
    rw [heq]
    apply Prod.ext
    · ext
      simp
    · ext
      simp

theorem embeddedCircleLocallyFlat_reparam_iff
    {M : Type} [TopologicalSpace M] (j : C(Circle, M))
    (e : Circle ≃ₜ Circle) :
    EmbeddedCircleLocallyFlat
      (j.comp (⟨e, e.continuous⟩ : C(Circle, Circle))) ↔
      EmbeddedCircleLocallyFlat j := by
  constructor
  · intro h z
    let k := j.comp (⟨e, e.continuous⟩ : C(Circle, Circle))
    have hk : k.comp (⟨e.symm, e.symm.continuous⟩ : C(Circle, Circle)) = j := by
      ext
      simp [k]
    have hz := EmbeddedCircleFlatNeighborhood.reparam k e.symm z
      (Classical.choice (h (e.symm z)))
    rw [hk] at hz
    exact ⟨hz⟩
  · intro h z
    exact ⟨EmbeddedCircleFlatNeighborhood.reparam j e z
      (Classical.choice (h (e z)))⟩

end ConstructionTargets.SurfaceSchoenflies
