import Mathlib
import ConstructionTargets.RealProjectiveSmoothTarget

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
