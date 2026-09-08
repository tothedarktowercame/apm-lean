import ConstructionTargets.SardConstantCoordinateSliceFlatness

open Filter
open scoped Topology
namespace SardEventuallyConstantCoordinateSliceFlatnessProbe

variable {E R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Eventual constancy of a coordinate near the base point forces the slice
derivative into the coordinate kernel. -/
theorem derivative_comp_eq_zero_of_coordinate_eventually_constant
    (p : E → R) (s : G → E) (r : R) (z : G)
    (P : E →L[ℝ] R) (J : G →L[ℝ] E)
    (hp : HasFDerivAt p P (s z)) (hs : HasFDerivAt s J z)
    (hconst : p ∘ s =ᶠ[𝓝 z] fun _ => r) : P.comp J = 0 := by
  have hc : HasFDerivAt (p ∘ s) (P.comp J) z := hp.comp z hs
  have hz : HasFDerivAt (p ∘ s) (0 : G →L[ℝ] R) z :=
    (hasFDerivAt_const (x := z) (c := r)).congr_of_eventuallyEq hconst
  exact hc.unique hz

/-- Residual flatness transports to a slice whose coordinate is only locally
constant, as supplied by a local inverse-chart identity. -/
theorem hasFDerivAt_zero_on_eventuallyConstantCoordinateSlice
    (h : E → S) (p : E → R) (s : G → E) (r : R) (z : G)
    (H : E →L[ℝ] S) (P : E →L[ℝ] R) (J : G →L[ℝ] E)
    (hh : HasFDerivAt h H (s z)) (hp : HasFDerivAt p P (s z))
    (hs : HasFDerivAt s J z)
    (hconst : p ∘ s =ᶠ[𝓝 z] fun _ => r)
    (hflat : ∀ v ∈ P.ker, H v = 0) :
    HasFDerivAt (h ∘ s) (0 : G →L[ℝ] S) z := by
  apply SardConstantCoordinateSliceFlatnessProbe.hasFDerivAt_zero_on_constantCoordinateSlice
    h s z H P J hh hs
  · exact derivative_comp_eq_zero_of_coordinate_eventually_constant
      p s r z P J hp hs hconst
  · exact hflat

#print axioms derivative_comp_eq_zero_of_coordinate_eventually_constant
#print axioms hasFDerivAt_zero_on_eventuallyConstantCoordinateSlice
end SardEventuallyConstantCoordinateSliceFlatnessProbe
