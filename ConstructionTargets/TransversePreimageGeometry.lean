import ConstructionTargets.TransverseLinearPair
import ConstructionTargets.TransversePreimageDuality

/-!
# Geometric producer interface for transverse-preimage duality

This module fixes the seam between differential transversality and the
homological `DetectsTopMap` conclusion.  It is independent of manifolds: a
consumer supplies two families of linear maps and an incidence relation, then
proves that their pointwise surjectivity produces the desired duality theorem.

The pointwise condition is intentionally abstract.  In particular, manifold
consumers can first translate a join of derivative ranges to operational
surjectivity of the coproduct derivative without forcing tangent spaces at
different points to be definitionally equal.
-/

open CategoryTheory

noncomputable section

namespace ConstructionTargets.TransversePreimageGeometry

/-- A pointwise geometric condition along an incidence relation.  Keeping the
condition as a proposition family (rather than fixing its linear-map types)
allows manifold tangent spaces to depend on the incident points. -/
def HoldsAlong {X Z : Type*} (incident condition : X → Z → Prop) : Prop :=
  ∀ x z, incident x z → condition x z

/-- Package a pointwise condition in the interface expected by a geometric
producer. -/
theorem holdsAlong_of_pointwise
    {X Z : Type*} (incident condition : X → Z → Prop)
    (h : ∀ x z, incident x z → condition x z) :
    HoldsAlong incident condition := h

/-- Apply a manifold-specific duality producer to a pointwise geometric
condition.  This is the reusable end-to-end adapter between the two sides of
the geometric seam. -/
theorem detectsTopMap_of_pointwise_condition
    {X Z : Type*}
    {D E : Type*} [Category D] [Category E]
    [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (incident condition : X → Z → Prop)
    (Hcircle : TopCat ⥤ D) (Htop : TopCat ⥤ E)
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) (c : C(Circle, B))
    (hproducer : HoldsAlong incident condition →
      TransversePreimageDuality.DetectsTopMap Hcircle Htop f c)
    (hcondition : ∀ x z, incident x z → condition x z) :
    TransversePreimageDuality.DetectsTopMap Hcircle Htop f c :=
  hproducer (holdsAlong_of_pointwise incident condition hcondition)

/-- Range-sum transversality along an incidence relation gives the operational
surjectivity condition for the coproduct linear map. -/
theorem holdsAlong_surjective_coprod_of_range_sup_eq_top
    {X Z R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (incident : X → Z → Prop)
    (L : X → M →ₗ[R] P) (K : Z → N →ₗ[R] P)
    (htrans : ∀ x z, incident x z →
      LinearMap.range (L x) ⊔ LinearMap.range (K z) = ⊤) :
    HoldsAlong incident
      (fun x z => Function.Surjective (LinearMap.coprod (L x) (K z))) := by
  intro x z hxz
  rw [← TransverseLinearPair.isTransversePair_iff_surjective_coprod]
  exact htrans x z hxz

/-- Feed the range-sum formulation of transversality directly to a duality
producer whose input is coproduct surjectivity. -/
theorem detectsTopMap_of_range_sup_eq_top
    {X Z R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    {D E : Type*} [Category D] [Category E]
    [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (incident : X → Z → Prop)
    (L : X → M →ₗ[R] P) (K : Z → N →ₗ[R] P)
    (Hcircle : TopCat ⥤ D) (Htop : TopCat ⥤ E)
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) (c : C(Circle, B))
    (hproducer : HoldsAlong incident
        (fun x z => Function.Surjective (LinearMap.coprod (L x) (K z))) →
      TransversePreimageDuality.DetectsTopMap Hcircle Htop f c)
    (htrans : ∀ x z, incident x z →
      LinearMap.range (L x) ⊔ LinearMap.range (K z) = ⊤) :
    TransversePreimageDuality.DetectsTopMap Hcircle Htop f c :=
  hproducer
    (holdsAlong_surjective_coprod_of_range_sup_eq_top incident L K htrans)

/-- Pointwise range-sum transversality implies surjectivity of the coproduct
linear map.  This directional form avoids unfolding the equivalence at each
geometric incidence point. -/
theorem surjective_coprod_of_range_sup_eq_top
    {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    {L : M →ₗ[R] P} {K : N →ₗ[R] P}
    (htrans : LinearMap.range L ⊔ LinearMap.range K = ⊤) :
    Function.Surjective (LinearMap.coprod L K) :=
  (TransverseLinearPair.isTransversePair_iff_surjective_coprod L K).mp htrans

end ConstructionTargets.TransversePreimageGeometry

#print axioms ConstructionTargets.TransversePreimageGeometry.holdsAlong_of_pointwise
#print axioms ConstructionTargets.TransversePreimageGeometry.detectsTopMap_of_pointwise_condition
#print axioms ConstructionTargets.TransversePreimageGeometry.holdsAlong_surjective_coprod_of_range_sup_eq_top
#print axioms ConstructionTargets.TransversePreimageGeometry.detectsTopMap_of_range_sup_eq_top
#print axioms ConstructionTargets.TransversePreimageGeometry.surjective_coprod_of_range_sup_eq_top
