import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology

/-! A precise construction target for the smooth structure on real projective
space. The underlying topology and sphere projection are already concrete.
A SmoothAtlas must make THIS projection a local diffeomorphism. We do not
postulate an inhabitant: consumers explicitly ask for one in their conclusion.
No embedding, transversality, or other problem conclusion is a field. -/

open scoped Manifold ContDiff
noncomputable section
namespace ConstructionTargets.RealProjectiveSmoothTarget
open ProjectiveSpaceTopology

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : E (n + 1)) 1

instance sphereDimension (n : ℕ) : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
  ⟨by simp [E]⟩

def sphereVector (n : ℕ) (p : Sphere n) : NonzeroVectors ℝ n :=
  ⟨fun i => p.val i, by
    intro h
    have hz : p.val = 0 := by ext i; exact congrFun h i
    have hn : ‖p.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using p.property
    rw [hz] at hn
    norm_num at hn⟩

def sphereProjection (n : ℕ) (p : Sphere n) : Space ℝ n :=
  quotientMap ℝ n (sphereVector n p)

/-- Compatibility fixes the usual quotient smooth structure, rather than an
arbitrary atlas on a named type. Constructing an inhabitant is explicit work. -/
structure SmoothAtlas (n : ℕ) where
  charts : ChartedSpace (E n) (Space ℝ n)
  smooth : letI := charts; IsManifold (𝓡 n) ∞ (Space ℝ n)
  quotient_localDiffeomorph : letI := charts;
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (sphereProjection n)

end ConstructionTargets.RealProjectiveSmoothTarget
