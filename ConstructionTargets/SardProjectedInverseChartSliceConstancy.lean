import ConstructionTargets.SardFirstDerivativeProjectedChartExplicitNeighborhood
import ConstructionTargets.SardEventuallyConstantCoordinateSliceFlatness

open Filter
open scoped Topology
namespace SardProjectedInverseChartSliceConstancyProbe

variable {E R G : Type*}
  [TopologicalSpace R] [TopologicalSpace G]

/-- An inverse-chart coordinate identity on a product neighborhood becomes an
eventual constant-coordinate identity on every fixed-first-coordinate slice. -/
theorem eventually_firstCoordinate_inverse_fixedSlice
    (einv : R × G → E) (p : E → R) (r : R) (z : G) (V : Set (R × G))
    (hV : V ∈ 𝓝 (r, z))
    (hinv : ∀ q ∈ V, p (einv q) = q.1) :
    (fun w => p (einv (r, w))) =ᶠ[𝓝 z] fun _ => r := by
  have hmem : ∀ᶠ w in 𝓝 z, (r, w) ∈ V :=
    (continuousAt_const.prodMk continuousAt_id).eventually hV
  filter_upwards [hmem] with w hw
  exact hinv (r, w) hw

#print axioms eventually_firstCoordinate_inverse_fixedSlice
end SardProjectedInverseChartSliceConstancyProbe
