import ConstructionTargets.DiskBoundedPreimageDuality

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
    TransversePreimageDuality.NonzeroTopMapHasNonNullWinding
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
  (TransversePreimageDuality.nonzeroTopMapHasNonNullWinding_iff_detectsTopMap
    _ _ f c).mp (hPD f c hf hc hcsmooth htrans)

set_option maxHeartbeats 800000 in
/-- End-to-end surface specialization: an oriented-surface duality producer,
range-sum transversality, essentiality of the embedded circle, and disk-bounded
inverse-image components force the integral top-homology map to vanish.

This theorem deliberately keeps the two homology computations explicit.  It
therefore applies to any compact connected charted surface once a consumer has
identified `H₁(S¹)` and the surface's `H₁`; no genus-specific definition is
built into the library interface. -/
theorem topHomologyMap_eq_zero_of_producer_and_componentsBoundByDisks
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
    (hPD : Producer S)
    (f : C(S, S)) (hf : ContMDiff I2 I2 ∞ f)
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) I2 ∞ c)
    {Q : Type} [AddCommGroup Q] [Module ℤ Q] [Module.IsTorsionFree ℤ Q]
    (eCircle : (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of Circle)) ≅ ModuleCat.of ℤ ℤ)
    (eS : (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of S)) ≅ ModuleCat.of ℤ Q)
    (hessential : ((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom c) ≠ 0)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range (mfderiv I2 I2 f x).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 1) I2 c z).toLinearMap = ⊤)
    (hdisks : DiskBoundaryHomology.ComponentsBoundByDisks
      (f ⁻¹' Set.range c)) :
    ((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f) = 0 := by
  let Htop := (AlgebraicTopology.singularHomologyFunctor
    (ModuleCat ℤ) 2).obj (ModuleCat.of ℤ ℤ)
  let L : S → E2 →ₗ[ℝ] E2 :=
    fun x => (mfderiv I2 I2 f x).toLinearMap
  let K : Circle → EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] E2 :=
    fun z => (mfderiv (𝓡 1) I2 c z).toLinearMap
  exact DiskBoundedPreimageDuality.map_eq_zero_of_range_sup_eq_top_and_componentsBoundByDisks_of_isos
    (ModuleCat.of ℤ ℤ) 1 one_ne_zero Htop
    (fun (x : S) (z : Circle) => f x = c z)
    L K
    f c hc eCircle eS hessential
    (fun hsurj => detectsTopMap hPD f c hf hc hcsmooth (by simpa [L, K] using hsurj))
    (by simpa [L, K] using htrans) hdisks

end ConstructionTargets.OrientedSurfacePreimageDuality

#print axioms ConstructionTargets.OrientedSurfacePreimageDuality.detectsTopMap
#print axioms ConstructionTargets.OrientedSurfacePreimageDuality.topHomologyMap_eq_zero_of_producer_and_componentsBoundByDisks
