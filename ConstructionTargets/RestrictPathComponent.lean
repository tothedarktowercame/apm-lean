import ConstructionTargets.CoveringRetainedSheetHomeomorph
import ConstructionTargets.CoveringPathConnectedChart
import ConstructionTargets.CoveringTotalLocPathConnected
import ConstructionTargets.CoveringPathComponentSurjective

open Set Topology Bundle

noncomputable section

namespace ConstructionTargets.RestrictPathComponent

open ConstructionTargets.CoveringRetainedSheetIndices
open ConstructionTargets.CoveringRetainedSheetHomeomorph
open ConstructionTargets.CoveringPathConnectedChart
open ConstructionTargets.CoveringPathComponentDomain
open ConstructionTargets.CoveringPathComponentSurjective
open ConstructionTargets.CoveringTotalLocPathConnected

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Restricting a surjective covering to a clopen subset of its domain is
again a covering, provided the base is locally path connected. -/
theorem restrictClopen_isCoveringMap [LocPathConnectedSpace B]
    {p : E → B} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (C : Set E) (hC : IsClopen C) :
    IsCoveringMap (fun z : C => p z.1) := by
  intro b
  obtain ⟨t, hb, hpath⟩ := hp.exists_pathConnected_restrictedTrivialization hsurj b
  letI : DiscreteTopology (p ⁻¹' {b}) := (hp b).discreteTopology_fiber
  letI : TopologicalSpace (RetainedIndex t C b hb) := by
    unfold RetainedIndex
    infer_instance
  letI : DiscreteTopology (RetainedIndex t C b hb) := by
    constructor
    change TopologicalSpace.induced Subtype.val inferInstance = ⊥
    have hF : (inferInstance : TopologicalSpace (p ⁻¹' {b})) = ⊥ :=
      DiscreteTopology.eq_bot
    rw [hF]
    apply TopologicalSpace.ext
    funext s
    apply propext
    change (∃ t : Set (p ⁻¹' {b}), True ∧ Subtype.val ⁻¹' t = s) ↔ True
    exact iff_true_intro ⟨Subtype.val '' s, trivial,
      Set.preimage_image_eq _ Subtype.val_injective⟩
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage
    (I := RetainedIndex t C b hb)
  refine ⟨inferInstance, t.baseSet, hb, t.open_baseSet, ?_,
    retainedSheetHomeomorph t C hC hpath b hb, ?_⟩
  · exact t.open_baseSet.preimage (hp.continuous.comp continuous_subtype_val)
  · intro z
    rfl

/-- A covering over a locally path-connected path-connected base restricts to
the Joined component of any chosen point as a surjective covering. -/
theorem IsCoveringMap.restrictPathComponent
    [LocPathConnectedSpace B] [PathConnectedSpace B]
    {p : E → B} (hp : IsCoveringMap p) (e : E) :
    IsCoveringMap (fun z : Component e => p z.1) ∧
      Function.Surjective (fun z : Component e => p z.1) := by
  letI : LocPathConnectedSpace E := hp.totalLocPathConnectedSpace
  have hCopen : IsOpen {x : E | Joined e x} := component_isOpen e
  have hC : IsClopen {x : E | Joined e x} :=
    ⟨IsClosed.pathComponent e, hCopen⟩
  have hcomp := componentProjection_surjective hp e
  have hsurj : Function.Surjective p := fun b => by
    obtain ⟨z, hz⟩ := hcomp b
    exact ⟨z.1, hz⟩
  exact ⟨restrictClopen_isCoveringMap hp hsurj _ hC, hcomp⟩

#print axioms restrictClopen_isCoveringMap
#print axioms IsCoveringMap.restrictPathComponent

end ConstructionTargets.RestrictPathComponent
