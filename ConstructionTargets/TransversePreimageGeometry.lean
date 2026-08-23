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

end ConstructionTargets.TransversePreimageGeometry

#print axioms ConstructionTargets.TransversePreimageGeometry.holdsAlong_of_pointwise
#print axioms ConstructionTargets.TransversePreimageGeometry.detectsTopMap_of_pointwise_condition
