import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.TransversePreimageDuality

/-!
# Disk-bounded embedded-circle preimages

This module joins two reusable halves of the transverse-preimage argument.
Disk fillings make the component circles trivial in positive-degree singular
homology.  An embedded target circle whose homology map is monic then makes
their lifted winding maps trivial.  Consequently any supplied duality
principle detects that the selected top map vanishes.
-/

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.DiskBoundedPreimageDuality

/-- Disk-bounded components of an embedded-circle preimage have null winding
for positive-degree singular homology, provided the embedded circle is
detected by a monomorphism. -/
theorem hasNullWindingPreimage_of_componentsBoundByDisks
    (C : Type*) [Category C] [Preadditive C] [Limits.HasCoproducts C]
    [CategoryWithHomology C]
    (A : C) (n : ℕ) (hn : n ≠ 0)
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    [Mono (((AlgebraicTopology.singularHomologyFunctor C n).obj A).map
      (TopCat.ofHom c))]
    (hdisks : DiskBoundaryHomology.ComponentsBoundByDisks (f ⁻¹' range c)) :
    EmbeddedCirclePreimage.HasNullWindingPreimage
      ((AlgebraicTopology.singularHomologyFunctor C n).obj A) f c := by
  apply EmbeddedCirclePreimage.hasNullWindingPreimage_of_components
    ((AlgebraicTopology.singularHomologyFunctor C n).obj A) f c hc
  intro x hx
  exact DiskBoundaryHomology.exists_homology_trivial_circle_through_point
    C A hdisks hx n hn

/-- A duality principle turns disk-bounded components of an embedded-circle
preimage into vanishing of the selected top map.  This is the end-to-end
categorical/homological interface; only the geometric duality principle must
be supplied by a manifold-specific consumer. -/
theorem map_eq_zero_of_componentsBoundByDisks
    (C : Type*) [Category C] [Preadditive C] [Limits.HasCoproducts C]
    [CategoryWithHomology C]
    (A : C) (n : ℕ) (hn : n ≠ 0)
    {E : Type*} [Category E] [Limits.HasZeroMorphisms E]
    (Htop : Functor TopCat E)
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    [Mono (((AlgebraicTopology.singularHomologyFunctor C n).obj A).map
      (TopCat.ofHom c))]
    (hduality : TransversePreimageDuality.DetectsTopMap
      ((AlgebraicTopology.singularHomologyFunctor C n).obj A) Htop f c)
    (hdisks : DiskBoundaryHomology.ComponentsBoundByDisks (f ⁻¹' range c)) :
    Htop.map (TopCat.ofHom f) = 0 := by
  apply TransversePreimageDuality.map_eq_zero
    ((AlgebraicTopology.singularHomologyFunctor C n).obj A) Htop f c hduality
  exact hasNullWindingPreimage_of_componentsBoundByDisks
    C A n hn f c hc hdisks

end ConstructionTargets.DiskBoundedPreimageDuality

#print axioms ConstructionTargets.DiskBoundedPreimageDuality.hasNullWindingPreimage_of_componentsBoundByDisks
#print axioms ConstructionTargets.DiskBoundedPreimageDuality.map_eq_zero_of_componentsBoundByDisks
