import ConstructionTargets.TransversePreimageGeometry

/-!
# Oriented-surface transverse-preimage duality interface

This module records the precise manifold theorem needed to turn transverse
inverse images of an embedded circle into detection of the top singular
homology map.  The actual Poincare-duality construction is intentionally the
single field of `Producer`; all conversions between derivative formulations
and the abstract homological seam remain proved library lemmas.
-/

open CategoryTheory
open scoped ContDiff Manifold

noncomputable section

namespace ConstructionTargets.OrientedSurfacePreimageDuality

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev I2 := 𝓘(ℝ, E2)

/-- The manifold-level Poincare-duality theorem for a compact connected
charted surface.  It is packaged independently of any genus computation or
disk-bounding assumption: those belong to downstream homological arguments.

The operational transversality input uses surjectivity of the coproduct of
the two derivatives, which is the form produced by
`TransversePreimageGeometry` from a sum-of-ranges hypothesis. -/
def Producer (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S] : Prop :=
  ∀ (f : C(S, S)) (c : C(Circle, S)),
    ContMDiff I2 I2 ∞ f →
    Topology.IsEmbedding c →
    ContMDiff (𝓡 1) I2 ∞ c →
    TransversePreimageGeometry.HoldsAlong
      (fun x z => f x = c z)
      (fun x z => Function.Surjective (LinearMap.coprod
        (mfderiv I2 I2 f x).toLinearMap
        (mfderiv (𝓡 1) I2 c z).toLinearMap)) →
    TransversePreimageDuality.DetectsTopMap
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ))
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)) f c

/-- Specialize a surface duality producer to one smooth transverse pair. -/
theorem detectsTopMap
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
    (hPD : Producer S) (f : C(S, S)) (c : C(Circle, S))
    (hf : ContMDiff I2 I2 ∞ f) (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) I2 ∞ c)
    (htrans : TransversePreimageGeometry.HoldsAlong
      (fun x z => f x = c z)
      (fun x z => Function.Surjective (LinearMap.coprod
        (mfderiv I2 I2 f x).toLinearMap
        (mfderiv (𝓡 1) I2 c z).toLinearMap))) :
    TransversePreimageDuality.DetectsTopMap
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ))
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)) f c :=
  hPD f c hf hc hcsmooth htrans

end ConstructionTargets.OrientedSurfacePreimageDuality

#print axioms ConstructionTargets.OrientedSurfacePreimageDuality.detectsTopMap
