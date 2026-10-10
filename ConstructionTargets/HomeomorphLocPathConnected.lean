import Mathlib.Topology.Connected.LocPathConnected

noncomputable section

namespace ConstructionTargets.HomeomorphLocPathConnected

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.locPathConnectedSpace (h : X ≃ₜ Y)
    [LocPathConnectedSpace Y] : LocPathConnectedSpace X := by
  exact h.symm.isQuotientMap.locPathConnectedSpace

theorem Homeomorph.locPathConnectedSpace_iff (h : X ≃ₜ Y) :
    LocPathConnectedSpace X ↔ LocPathConnectedSpace Y := by
  constructor
  · intro hX
    letI : LocPathConnectedSpace X := hX
    exact h.isQuotientMap.locPathConnectedSpace
  · intro hY
    letI : LocPathConnectedSpace Y := hY
    exact Homeomorph.locPathConnectedSpace h

#print axioms Homeomorph.locPathConnectedSpace
#print axioms Homeomorph.locPathConnectedSpace_iff

end ConstructionTargets.HomeomorphLocPathConnected
