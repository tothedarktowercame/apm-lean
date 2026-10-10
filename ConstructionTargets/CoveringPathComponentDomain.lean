import Mathlib.Topology.Connected.LocPathConnected

open Set
noncomputable section

namespace ConstructionTargets.CoveringPathComponentDomain

variable {E : Type*} [TopologicalSpace E]

abbrev Component (e : E) := {x : E // Joined e x}

theorem component_set_eq (e : E) : {x : E | Joined e x} = pathComponent e := rfl

theorem component_isOpen [LocPathConnectedSpace E] (e : E) :
    IsOpen {x : E | Joined e x} := by
  rw [component_set_eq]
  exact IsOpen.pathComponent e

theorem component_isPathConnected (e : E) :
    IsPathConnected {x : E | Joined e x} := by
  rw [component_set_eq]
  exact isPathConnected_pathComponent

noncomputable instance componentPathConnectedSpace (e : E) :
    PathConnectedSpace (Component e) := by
  exact isPathConnected_iff_pathConnectedSpace.mp (component_isPathConnected e)

#print axioms component_set_eq
#print axioms component_isOpen
#print axioms component_isPathConnected
#print axioms componentPathConnectedSpace

end ConstructionTargets.CoveringPathComponentDomain
