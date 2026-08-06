import Mathlib

/-!
# APM m01J01 — Open Mapping and Closed Graph Theorems

## Statement repairs

None.

## Encoding notes

The statements are made over real Banach spaces.  The Open Mapping Theorem uses
a continuous linear map and topological openness; the Closed Graph Theorem uses
an a priori merely linear map and closedness of its actual graph in `X × Y`.
-/

open Set

def apm_m01j01_OpenMappingTheorem : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace ℝ X] [NormedSpace ℝ Y] [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℝ] Y), Function.Surjective T → IsOpenMap T

def apm_m01j01_ClosedGraphTheorem : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace ℝ X] [NormedSpace ℝ Y] [CompleteSpace X] [CompleteSpace Y]
    (T : X →ₗ[ℝ] Y),
      IsClosed {p : X × Y | p.2 = T p.1} → Continuous T

theorem apm_m01j01 :
    apm_m01j01_OpenMappingTheorem ∧
    apm_m01j01_ClosedGraphTheorem ∧
    (apm_m01j01_OpenMappingTheorem → apm_m01j01_ClosedGraphTheorem) := by
  constructor
  · intro X Y _ _ _ _ _ _ T hT
    exact T.isOpenMap hT
  · constructor
    · intro X Y _ _ _ _ _ _ T hT
      apply T.continuous_of_isClosed_graph
      simpa [LinearMap.graph, eq_comm] using hT

    · intro _ X Y _ _ _ _ _ _ T hT
      apply T.continuous_of_isClosed_graph
      simpa [LinearMap.graph, eq_comm] using hT
