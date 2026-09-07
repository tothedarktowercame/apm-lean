import Mathlib

/-! # APM m98J01: open mapping and closed graph theorems

## Statement repairs

The scalar field is made explicit and restricted to `ℝ` or `ℂ` through
`IsROrC`, as in the standard Banach-space formulations.

## Encoding questions

The graph of an everywhere-defined linear map is represented literally as
`{p : X × Y | p.2 = T p.1}`.  The third part packages the open mapping theorem
as a hypothesis and asks for continuity from a closed graph.
-/

/-- The open mapping theorem. -/
theorem apm_m98j01_open_mapping
    {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (S : X →L[𝕜] Y) (hS : Function.Surjective S) :
    IsOpenMap S := by
  sorry

/-- The closed graph theorem for an everywhere-defined linear map. -/
theorem apm_m98j01_closed_graph
    {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (T : X →ₗ[𝕜] Y) (hT : IsClosed {p : X × Y | p.2 = T p.1}) :
    Continuous T := by
  sorry

/-- Assuming the open mapping theorem for Banach spaces implies the closed
graph theorem. -/
theorem apm_m98j01_closed_graph_of_open_mapping
    (openMapping : ∀ {X Y : Type*},
      [NormedAddCommGroup X] → [NormedSpace ℝ X] → [CompleteSpace X] →
      [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → [CompleteSpace Y] →
      ∀ S : X →L[ℝ] Y, Function.Surjective S → IsOpenMap S)
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T : X →ₗ[ℝ] Y) (hT : IsClosed {p : X × Y | p.2 = T p.1}) :
    Continuous T := by
  sorry
