import ConstructionTargets.LocPathConnectedOpenCover
import Mathlib.Topology.Covering.Basic

open Set

noncomputable section

namespace ConstructionTargets.CoveringTotalLocPathConnected

open ConstructionTargets.HomeomorphLocPathConnected
open ConstructionTargets.LocPathConnectedOpenCover

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A local homeomorphism into a locally path-connected space has locally
path-connected domain. -/
theorem IsLocalHomeomorph.locPathConnectedSpace {f : E → B}
    (hf : IsLocalHomeomorph f) [LocPathConnectedSpace B] :
    LocPathConnectedSpace E := by
  apply locPathConnectedSpace_of_open_cover
  intro e
  obtain ⟨h, he, _⟩ := hf e
  refine ⟨h.source, h.open_source, he, ?_⟩
  letI : LocPathConnectedSpace h.target := h.open_target.locPathConnectedSpace
  exact Homeomorph.locPathConnectedSpace h.toHomeomorphSourceTarget

/-- The total space of a covering over a locally path-connected base is
locally path connected. -/
theorem IsCoveringMap.totalLocPathConnectedSpace {p : E → B}
    (hp : IsCoveringMap p) [LocPathConnectedSpace B] :
    LocPathConnectedSpace E :=
  IsLocalHomeomorph.locPathConnectedSpace hp.isLocalHomeomorph

#print axioms IsLocalHomeomorph.locPathConnectedSpace
#print axioms IsCoveringMap.totalLocPathConnectedSpace

end ConstructionTargets.CoveringTotalLocPathConnected
