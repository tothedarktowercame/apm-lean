import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.IntegerCyclic
import ConstructionTargets.TransversePreimageDuality
import ConstructionTargets.TransversePreimageGeometry

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

/-- A pointwise geometric condition, a producer translating that condition to
duality, and disk-bounded preimage components force the selected top map to
vanish.  This version supports dependent geometric data by leaving the
condition as a proposition family. -/
theorem map_eq_zero_of_pointwise_condition_and_componentsBoundByDisks
    (C : Type*) [Category C] [Preadditive C] [Limits.HasCoproducts C]
    [CategoryWithHomology C]
    (A : C) (n : ℕ) (hn : n ≠ 0)
    {E : Type*} [Category E] [Limits.HasZeroMorphisms E]
    (Htop : Functor TopCat E)
    {X Z : Type*} (incident condition : X → Z → Prop)
    {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    (f : C(Y, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    [Mono (((AlgebraicTopology.singularHomologyFunctor C n).obj A).map
      (TopCat.ofHom c))]
    (hproducer : TransversePreimageGeometry.HoldsAlong incident condition →
      TransversePreimageDuality.DetectsTopMap
        ((AlgebraicTopology.singularHomologyFunctor C n).obj A) Htop f c)
    (hcondition : ∀ x z, incident x z → condition x z)
    (hdisks : DiskBoundaryHomology.ComponentsBoundByDisks (f ⁻¹' range c)) :
    Htop.map (TopCat.ofHom f) = 0 := by
  apply map_eq_zero_of_componentsBoundByDisks C A n hn Htop f c hc
  · exact TransversePreimageGeometry.detectsTopMap_of_pointwise_condition
      incident condition
      ((AlgebraicTopology.singularHomologyFunctor C n).obj A) Htop
      f c hproducer hcondition
  · exact hdisks

/-- Range-sum transversality, a producer translating its operational coproduct
surjectivity form to duality, and disk-bounded preimage components force the
selected top map to vanish. -/
theorem map_eq_zero_of_range_sup_eq_top_and_componentsBoundByDisks
    (C : Type*) [Category C] [Preadditive C] [Limits.HasCoproducts C]
    [CategoryWithHomology C]
    (A : C) (n : ℕ) (hn : n ≠ 0)
    {E : Type*} [Category E] [Limits.HasZeroMorphisms E]
    (Htop : Functor TopCat E)
    {X Z R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (incident : X → Z → Prop)
    (L : X → M →ₗ[R] P) (K : Z → N →ₗ[R] P)
    {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    (f : C(Y, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    [Mono (((AlgebraicTopology.singularHomologyFunctor C n).obj A).map
      (TopCat.ofHom c))]
    (hproducer : TransversePreimageGeometry.HoldsAlong incident
        (fun x z => Function.Surjective (LinearMap.coprod (L x) (K z))) →
      TransversePreimageDuality.DetectsTopMap
        ((AlgebraicTopology.singularHomologyFunctor C n).obj A) Htop f c)
    (htrans : ∀ x z, incident x z →
      LinearMap.range (L x) ⊔ LinearMap.range (K z) = ⊤)
    (hdisks : DiskBoundaryHomology.ComponentsBoundByDisks (f ⁻¹' range c)) :
    Htop.map (TopCat.ofHom f) = 0 := by
  apply map_eq_zero_of_pointwise_condition_and_componentsBoundByDisks
    C A n hn Htop incident
    (fun x z => Function.Surjective (LinearMap.coprod (L x) (K z)))
    f c hc hproducer
  · exact TransversePreimageGeometry.holdsAlong_surjective_coprod_of_range_sup_eq_top
      incident L K htrans
  · exact hdisks

/-- Integral specialization of the range-sum eliminator in which essentiality
of the target circle supplies the monomorphism automatically.  This is the
consumer-depth interface for surface arguments: computations identifying the
circle homology with `ℤ` and the ambient degree-one homology with a torsion-free
module, together with nonvanishing of the circle inclusion, discharge all
categorical cancellation bookkeeping. -/
theorem map_eq_zero_of_range_sup_eq_top_and_componentsBoundByDisks_of_isos
    (A : ModuleCat ℤ) (n : ℕ) (hn : n ≠ 0)
    {E : Type*} [Category E] [Limits.HasZeroMorphisms E]
    (Htop : Functor TopCat E)
    {X Z M N P : Type*} {Q : Type}
    [AddCommGroup Q] [Module ℤ Q] [Module.IsTorsionFree ℤ Q]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module ℝ M] [Module ℝ N] [Module ℝ P]
    (incident : X → Z → Prop)
    (L : X → M →ₗ[ℝ] P) (K : Z → N →ₗ[ℝ] P)
    {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    (f : C(Y, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (eCircle : (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) n).obj A).obj (TopCat.of Circle)) ≅ ModuleCat.of ℤ ℤ)
    (eS : (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) n).obj A).obj (TopCat.of S)) ≅ ModuleCat.of ℤ Q)
    (hessential : ((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) n).obj A).map (TopCat.ofHom c) ≠ 0)
    (hproducer : TransversePreimageGeometry.HoldsAlong incident
        (fun x z => Function.Surjective (LinearMap.coprod (L x) (K z))) →
      TransversePreimageDuality.DetectsTopMap
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj A)
        Htop f c)
    (htrans : ∀ x z, incident x z →
      LinearMap.range (L x) ⊔ LinearMap.range (K z) = ⊤)
    (hdisks : DiskBoundaryHomology.ComponentsBoundByDisks (f ⁻¹' range c)) :
    Htop.map (TopCat.ofHom f) = 0 := by
  letI : Mono (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat ℤ) n).obj A).map (TopCat.ofHom c)) :=
    IntegerCyclic.mono_of_ne_zero_of_iso Q eCircle eS _ hessential
  exact map_eq_zero_of_range_sup_eq_top_and_componentsBoundByDisks
    (ModuleCat ℤ) A n hn Htop incident L K f c hc hproducer htrans hdisks

/-- Convert one range-sum transversality witness into the operational
surjectivity condition consumed by the disk-bounded duality theorem. -/
theorem surjective_coprod_of_range_sup_eq_top
    {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    {L : M →ₗ[R] P} {K : N →ₗ[R] P}
    (htrans : LinearMap.range L ⊔ LinearMap.range K = ⊤) :
    Function.Surjective (LinearMap.coprod L K) :=
  TransversePreimageGeometry.surjective_coprod_of_range_sup_eq_top htrans

end ConstructionTargets.DiskBoundedPreimageDuality

#print axioms ConstructionTargets.DiskBoundedPreimageDuality.hasNullWindingPreimage_of_componentsBoundByDisks
#print axioms ConstructionTargets.DiskBoundedPreimageDuality.map_eq_zero_of_componentsBoundByDisks
#print axioms ConstructionTargets.DiskBoundedPreimageDuality.map_eq_zero_of_pointwise_condition_and_componentsBoundByDisks
#print axioms ConstructionTargets.DiskBoundedPreimageDuality.map_eq_zero_of_range_sup_eq_top_and_componentsBoundByDisks
#print axioms ConstructionTargets.DiskBoundedPreimageDuality.map_eq_zero_of_range_sup_eq_top_and_componentsBoundByDisks_of_isos
#print axioms ConstructionTargets.DiskBoundedPreimageDuality.surjective_coprod_of_range_sup_eq_top
