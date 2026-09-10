import Mathlib
import ConstructionTargets.RealProjectiveSmoothTarget

/-! # t95A04: the projective-plane Veronese embedding

The existence of the quotient-compatible smooth atlas is an explicit
construction requirement in the conclusion, not an assumed arbitrary manifold.
The descended map is constrained at every sphere representative to equal the
six printed coordinates. Smoothness, topological embedding and immersion
retain the full smooth-submanifold conclusion. IsImmersion uses Mathlib's
local coordinate normal form, not just a renamed injectivity predicate.
-/

open scoped Manifold ContDiff
open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.RealProjectiveSmoothTarget
noncomputable section

def T95A04SphereMap (p : Sphere 2) : E 6 :=
  WithLp.toLp 2 ![p.val 0 ^ 2, p.val 1 ^ 2, p.val 2 ^ 2,
    p.val 0 * p.val 1, p.val 0 * p.val 2, p.val 1 * p.val 2]

theorem apm_t95a04 :
    ∃ atlas : SmoothAtlas 2,
    letI := atlas.charts
    letI := atlas.smooth
    ∃ f : Space ℝ 2 → E 6,
      (∀ p : Sphere 2, f (sphereProjection 2 p) = T95A04SphereMap p) ∧
      ContMDiff (𝓡 2) (𝓡 6) ∞ f ∧ Topology.IsEmbedding f ∧
      Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ f := by
  sorry
