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

end ConstructionTargets.SurfaceSchoenflies
