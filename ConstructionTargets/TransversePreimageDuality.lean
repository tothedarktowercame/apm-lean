import ConstructionTargets.EmbeddedCirclePreimage

/-!
# The abstract transverse-preimage duality seam

This module separates the categorical input to a transverse-preimage argument
from its geometric Poincare-duality theorem.  The degree-one functor records
winding around an embedded circle; the top-degree functor records the map whose
vanishing is sought.

The predicate below is deliberately a property of a particular map and target
circle.  This keeps differential-topological hypotheses (smoothness,
transversality, orientations, and dimension) out of the categorical module,
while giving their eventual theorem a stable conclusion to produce.
-/

open CategoryTheory

noncomputable section

namespace ConstructionTargets.TransversePreimageDuality

/-- A transverse-preimage duality principle for a particular map and circle:
null winding of all parametrized inverse-image components forces the map on
the selected top-degree functor to vanish.  Geometry supplies this property;
`map_eq_zero` below is its reusable elimination rule. -/
def DetectsTopMap
    {D E : Type*} [Category D] [Category E]
    [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (Hcircle : TopCat ⥤ D) (Htop : TopCat ⥤ E)
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) : Prop :=
  EmbeddedCirclePreimage.HasNullWindingPreimage Hcircle f c →
    Htop.map (TopCat.ofHom f) = 0

/-- Apply a transverse-preimage duality principle to its null-winding input. -/
theorem map_eq_zero
    {D E : Type*} [Category D] [Category E]
    [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (Hcircle : TopCat ⥤ D) (Htop : TopCat ⥤ E)
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S))
    (hduality : DetectsTopMap Hcircle Htop f c)
    (hpreimage : EmbeddedCirclePreimage.HasNullWindingPreimage Hcircle f c) :
    Htop.map (TopCat.ofHom f) = 0 :=
  hduality hpreimage

end ConstructionTargets.TransversePreimageDuality

#print axioms ConstructionTargets.TransversePreimageDuality.map_eq_zero
