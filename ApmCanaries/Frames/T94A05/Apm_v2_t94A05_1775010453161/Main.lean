import Mathlib
import ApmCanaries.Frames.T94A05.Apm_v2_t94A05_1775010453161.Scratch

noncomputable section

open scoped Topology

namespace ApmCanaries.Frames.T94A05.Apm_v2_t94A05_1775010453161.Main

/-- Convenience lemma: a connected, locally path connected space is
path connected as a set (`IsPathConnected univ`). -/
lemma isPathConnected_univ_of_connected
    (M : Type*) [TopologicalSpace M]
    [LocPathConnectedSpace M] [ConnectedSpace M] :
    IsPathConnected (Set.univ : Set M) := by
  classical
  have hPathConnectedSpace :
      PathConnectedSpace M :=
    (pathConnectedSpace_iff_connectedSpace).2 inferInstance
  exact (pathConnectedSpace_iff_univ (X := M)).1 hPathConnectedSpace

/-- On any charted space whose model space is locally path connected,
global connectedness implies global path connectedness.  This is the Lean
counterpart of “connected manifold ⇒ path connected.” -/
theorem connected_manifold_path_connected
    (H M : Type*) [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [LocPathConnectedSpace H] [ConnectedSpace M] :
    PathConnectedSpace M := by
  classical
  have _ : LocPathConnectedSpace M :=
    ChartedSpace.locPathConnectedSpace (H := H) (M := M)
  exact (pathConnectedSpace_iff_connectedSpace).2 inferInstance

end ApmCanaries.Frames.T94A05.Apm_v2_t94A05_1775010453161.Main
