import Mathlib
import ConstructionTargets.RealProjectiveSmoothTarget
import ConstructionTargets.t96A07Closure

/-! # t96A07: transversality of the quadratic sphere/projective-plane map

All coordinates, the z-axis and the horizontal planes are concrete. The
quotient-compatible smooth atlas is an existential construction target.
Transversality is the spanning condition on actual derivatives at incident
points; no arbitrary transversality proposition is supplied. Part (b) uses
the descended map, while part (c) uses the original sphere map as printed.
-/

open scoped Manifold ContDiff
open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.RealProjectiveSmoothTarget
open Set
noncomputable section
namespace T96A07

def sphereMap (p : Sphere 2) : E 3 :=
  WithLp.toLp 2 ![p.val 1 * p.val 2, p.val 0 * p.val 2, p.val 0 * p.val 1]

def axis (t : ℝ) : E 3 := WithLp.toLp 2 ![0, 0, t]
def plane (z : ℝ) (p : E 2) : E 3 := WithLp.toLp 2 ![p 0, p 1, z]

def Transverse {M V : Type*} [TopologicalSpace M] [ChartedSpace (E 2) M]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : M → E 3) (g : V → E 3) : Prop :=
  ∀ x y, f x = g y →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 3) f x).toLinearMap ⊔
      LinearMap.range (fderiv ℝ g y).toLinearMap = ⊤

end T96A07

namespace ConstructionTargets.T96A07Closure

theorem sphereMap_antipodal (p : Sphere 2) :
    T96A07.sphereMap (sphereAntipodalN 2 p) = T96A07.sphereMap p := by
  simpa [T96A07.sphereMap,
    crossTermSphereMap] using
    crossTermSphereMap_antipodal p

theorem sphereMap_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ∞ T96A07.sphereMap := by
  simpa [T96A07.sphereMap, crossTermSphereMap] using
    crossTermSphereMap_contMDiff

theorem descendedSphereMap :
    letI := rpSmoothAtlas.charts
    letI := rpSmoothAtlas.smooth
    ∃ f : Space ℝ 2 → E 3,
      (∀ p : Sphere 2, f (sphereProjection 2 p) = T96A07.sphereMap p) ∧
      ContMDiff (𝓡 2) (𝓡 3) ∞ f := by
  simpa [T96A07.sphereMap, crossTermSphereMap] using
    crossTermSphereMap_descends

theorem sphereMap_mfderiv_e0_range :
    LinearMap.range
        (mfderiv (𝓡 2) (𝓡 3) T96A07.sphereMap sphereFirstPoint).toLinearMap =
      yzCoordinatePlane := by
  simpa [T96A07.sphereMap, crossTermSphereMap] using
    crossTermSphereMap_mfderiv_firstPoint_range

theorem descended_mfderiv_range_at_e0
    (f : Space ℝ 2 → E 3)
    (hfac : ∀ p : Sphere 2, f (sphereProjection 2 p) = T96A07.sphereMap p) :
    letI := rpSmoothAtlas.charts
    letI := rpSmoothAtlas.smooth
    ContMDiff (𝓡 2) (𝓡 3) ∞ f →
    LinearMap.range
        (mfderiv (𝓡 2) (𝓡 3) f (sphereProjection 2 sphereFirstPoint)).toLinearMap =
      yzCoordinatePlane := by
  simpa [T96A07.sphereMap, crossTermSphereMap] using
    descendedCrossTermMap_mfderiv_range_at_e0 f hfac

theorem descended_not_transverse_axis
    (f : Space ℝ 2 → E 3)
    (hfac : ∀ p : Sphere 2, f (sphereProjection 2 p) = T96A07.sphereMap p) :
    letI := rpSmoothAtlas.charts
    letI := rpSmoothAtlas.smooth
    ContMDiff (𝓡 2) (𝓡 3) ∞ f →
    ¬ T96A07.Transverse f T96A07.axis := by
  letI := rpSmoothAtlas.charts
  letI := rpSmoothAtlas.smooth
  intro hf htransverse
  have hbad := descendedCrossTermMap_notTransverse_zAxis f
    (by simpa [T96A07.sphereMap, crossTermSphereMap] using hfac) hf
  rcases hbad with ⟨x, y, hxy, hspan⟩
  apply hspan
  exact htransverse x y (by simpa [T96A07.axis, zAxis] using hxy)

theorem plane_fderiv_range (z : ℝ) (p : E 2) :
    LinearMap.range (fderiv ℝ (T96A07.plane z) p).toLinearMap =
      xyCoordinatePlane := by
  simpa [T96A07.plane, horizontalPlane] using
    horizontalPlane_fderiv_range z p

theorem sphereMap_plane_incident_coordinates
    (p : Sphere 2) (z : ℝ) (q : E 2)
    (hinc : T96A07.sphereMap p = T96A07.plane z q) (hz : 0 < z) :
    p.val 0 * p.val 1 = z ∧ p.val 0 ≠ 0 ∧ p.val 1 ≠ 0 := by
  apply crossTerm_horizontalPlane_incident_coordinates p z q
  · simpa [T96A07.sphereMap, crossTermSphereMap,
      T96A07.plane, horizontalPlane] using hinc
  · exact hz

theorem sphereMap_vertical_surjective
    (p : Sphere 2) (z : ℝ) (q : E 2)
    (hinc : T96A07.sphereMap p = T96A07.plane z q)
    (hz : 0 < z) (hzhalf : z < 1 / 2) :
    Function.Surjective
      (fun y : LinearMap.range
          (mfderiv (𝓡 2) (𝓡 3) T96A07.sphereMap p).toLinearMap =>
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (T96A07.sphereMap p) y.1) 2) := by
  simpa [T96A07.sphereMap, crossTermSphereMap] using
    crossTermSphereMap_vertical_surjective p z q
      (by simpa [T96A07.sphereMap, crossTermSphereMap,
        T96A07.plane, horizontalPlane] using hinc) hz hzhalf

#print axioms sphereMap_antipodal
#print axioms sphereMap_contMDiff
#print axioms descendedSphereMap
#print axioms sphereMap_mfderiv_e0_range
#print axioms descended_mfderiv_range_at_e0
#print axioms descended_not_transverse_axis
#print axioms plane_fderiv_range
#print axioms sphereMap_plane_incident_coordinates
#print axioms sphereMap_vertical_surjective

end ConstructionTargets.T96A07Closure

theorem apm_t96a07 :
    ∃ atlas : SmoothAtlas 2,
    letI := atlas.charts
    letI := atlas.smooth
    ∃ f : Space ℝ 2 → E 3,
      (∀ p : Sphere 2, f (sphereProjection 2 p) = T96A07.sphereMap p) ∧
      ContMDiff (𝓡 2) (𝓡 3) ∞ f ∧
      ¬ T96A07.Transverse f T96A07.axis ∧
      {z : ℝ | T96A07.Transverse T96A07.sphereMap (T96A07.plane z) ∧
        ∃ p : Sphere 2, T96A07.sphereMap p 2 = z}.Infinite := by
  sorry
