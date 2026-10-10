import ConstructionTargets.HomeomorphLocPathConnected

open Set Topology

noncomputable section

namespace ConstructionTargets.LocPathConnectedOpenCover

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Local path connectedness can be checked on an open neighborhood of each point. -/
theorem locPathConnectedSpace_of_open_cover
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ LocPathConnectedSpace U) :
    LocPathConnectedSpace X := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  obtain ⟨U, hU, hxU, hU_lpc⟩ := h x
  let xU : U := ⟨x, hxU⟩
  letI : LocPathConnectedSpace U := hU_lpc
  let v : Set U := pathComponentIn (Subtype.val ⁻¹' u) xU
  have hxpre : xU ∈ Subtype.val ⁻¹' u := hxu
  have hv_open : IsOpen v := (hu.preimage continuous_subtype_val).pathComponentIn xU
  have hv_mem : xU ∈ v := mem_pathComponentIn_self hxpre
  have himage_open : IsOpen (Subtype.val '' v) :=
    hU.isOpenEmbedding_subtypeVal.isOpenMap _ hv_open
  have hx_image : x ∈ Subtype.val '' v := ⟨xU, hv_mem, rfl⟩
  apply Filter.mem_of_superset (himage_open.mem_nhds hx_image)
  apply IsPathConnected.subset_pathComponentIn
  · exact (isPathConnected_pathComponentIn hxpre).image continuous_subtype_val
  · exact hx_image
  · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset Subtype.val)

#print axioms locPathConnectedSpace_of_open_cover

end ConstructionTargets.LocPathConnectedOpenCover
