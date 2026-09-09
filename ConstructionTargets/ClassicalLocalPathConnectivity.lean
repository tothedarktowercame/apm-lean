import Mathlib
import ConstructionTargets.CircleUniversalCover
noncomputable section
open Set Topology Filter ContinuousMap
namespace ConstructionTargets.ClassicalLocalPathConnectivity

theorem locPathConnected_of_classical {X : Type*} [TopologicalSpace X]
    (hX : LocallyContractibleSpace X) : LocPathConnectedSpace X := by
  apply locPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr
  intro x U hU hx
  obtain ⟨V, hVU, hV, c, ⟨H⟩⟩ := hX x U (hU.mem_nhds hx)
  apply Filter.mem_of_superset hV
  intro y hy
  have hxV : x ∈ V := mem_of_mem_nhds hV
  apply (joinedIn_iff_joined hx (hVU hy)).mpr
  exact ⟨(H.evalAt ⟨x, hxV⟩).trans (H.evalAt ⟨y, hy⟩).symm⟩


theorem component_locPathConnected {X : Type*} [TopologicalSpace X]
    (hX : LocallyContractibleSpace X) (x : X) :
    LocPathConnectedSpace (connectedComponent x) := by
  letI := locPathConnected_of_classical hX
  exact (isOpen_connectedComponent (x := x)).locPathConnectedSpace

theorem component_pathConnected {X : Type*} [TopologicalSpace X]
    (hX : LocallyContractibleSpace X) (x : X) :
    PathConnectedSpace (connectedComponent x) := by
  letI := component_locPathConnected hX x
  letI := Subtype.connectedSpace (isConnected_connectedComponent (x := x))
  exact PathConnectedSpace.of_locPathConnectedSpace

def componentMap {X : Type} [TopologicalSpace X] (f : C(X, Circle)) (x : X) :
    C(connectedComponent x, Circle) := f.comp ⟨Subtype.val, continuous_subtype_val⟩

theorem component_real_lift {X : Type} [TopologicalSpace X]
    (hX : LocallyContractibleSpace X) (f : C(X, Circle)) (x : X) (hx : f x = 1)
    (hloop : ∀ p : FundamentalGroup (connectedComponent x) ⟨x, mem_connectedComponent⟩,
      FundamentalGroup.map (componentMap f x) ⟨x, mem_connectedComponent⟩ p = 1) :
    ∃ F : C(connectedComponent x, ℝ),
      F ⟨x, mem_connectedComponent⟩ = 0 ∧
      ∀ y : connectedComponent x, Circle.exp (F y) = f y.val := by
  letI := component_locPathConnected hX x
  letI := component_pathConnected hX x
  have he : CircleUniversalCover.circleCover 0 =
      componentMap f x ⟨x, mem_connectedComponent⟩ := by
    simpa [CircleUniversalCover.circleCover, componentMap] using hx.symm
  obtain ⟨F, hF, _⟩ := CircleUniversalCover.circleCover_isCoveringMap.existsUnique_continuousMap_lifts_of_range_le
    he (by
      rintro z ⟨p, rfl⟩
      rw [hloop p]
      exact Subgroup.one_mem _)
  exact ⟨F, hF.1, fun y => congrFun hF.2 y⟩

end ConstructionTargets.ClassicalLocalPathConnectivity
#print axioms ConstructionTargets.ClassicalLocalPathConnectivity.locPathConnected_of_classical

#print axioms ConstructionTargets.ClassicalLocalPathConnectivity.component_locPathConnected
#print axioms ConstructionTargets.ClassicalLocalPathConnectivity.component_pathConnected

#print axioms ConstructionTargets.ClassicalLocalPathConnectivity.component_real_lift
