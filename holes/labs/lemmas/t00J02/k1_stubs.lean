import Mathlib
import ConstructionTargets.RelativeSingularConnectingNaturality
import ConstructionTargets.HigherChartLocalGenerator
import ConstructionTargets.OneDimensionalChartLocalGenerator
import ConstructionTargets.CollaredConnectedSumHomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CircleHomology
import ConstructionTargets.IntegerCyclic
import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.DiskBoundedPreimageDuality
import ConstructionTargets.EmbeddedCircleLift
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.TransversePreimageDuality
import ConstructionTargets.TransverseLinearPair
import ConstructionTargets.TransversePreimageGeometry
import ConstructionTargets.OrientedSurfacePreimageDuality
import ConstructionTargets.t00J02Closure
import ConstructionTargets.CircleActualLocalization

/-!
# Blueprint for APM t00J02

The existing `OrientedSurfacePreimageDuality.Producer` route is deliberately
not used: that contract is false.  The missing input is isolated as a direct
library theorem about the top-homology map of a transverse surface map.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

/-- Boundary-flattening map near `t` on the unit circle, recentred at a point on the inward normal. -/
def flatRecentred (t : Circle) : C(E2, E2) :=
  ⟨fun p => complexToE2 ((t : ℂ) * (Complex.exp ((p 0 : ℂ) * Complex.I) - 1 - (p 1 : ℂ))), by
    apply continuous_complexToE2.comp
    have h0 : Continuous fun p : E2 => ((p 0 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)
    have h1 : Continuous fun p : E2 => ((p 1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
    fun_prop⟩

theorem flatRecentred_localDegree (t : Circle) (V : Set E2) (hV : IsOpen V) (h0 : (0 : E2) ∈ V)
    (hVstrip : ∀ p ∈ V, |p 0| < Real.pi)
    (hz : ∀ p : V, flatRecentred t p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo V (flatRecentred t) hz 1 := by
  sorry

theorem chart_transition_degree
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [PathConnectedSpace S]
    [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]
    (e : apm_t00j02_H 2 S ≅ ModuleCat.of ℤ ℤ)
    (α β : OpenPartialHomeomorph S E2) (x : S)
    (hxα : x ∈ α.source) (hα0 : α x = 0) (hxβ : x ∈ β.source) (hβ0 : β x = 0)
    (U : Set E2) (hUo : IsOpen U) (h0U : (0 : E2) ∈ U) (hUα : U ⊆ α.target)
    (hUβ : ∀ p ∈ U, α.symm p ∈ β.source)
    (F : C(E2, E2)) (hF : ∀ p ∈ U, F p = β (α.symm p))
    (hzero : ∀ p : U, F p = 0 ↔ (p : E2) = 0)
    (sα sβ : ℤ) (hsα : IsChartSign e α x hxα hα0 sα)
    (hsβ : IsChartSign e β x hxβ hβ0 sβ) (hsβ1 : sβ = 1 ∨ sβ = -1) :
    IsLocalDegreeTwo U F hzero (sα * sβ) := by
  sorry

end t00J02_ModelProduct
