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

/-- Contrapositive, geometric form of top-map detection: whenever the selected
top map is nonzero, the inverse image cannot have null winding everywhere.

This is the useful output shape for an intersection-pairing argument: pairing
a nonzero pushed-forward fundamental class with the target circle must produce
at least one inverse-image component with nonzero winding. -/
def NonzeroTopMapHasNonNullWinding
    {D E : Type*} [Category D] [Category E]
    [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (Hcircle : TopCat ⥤ D) (Htop : TopCat ⥤ E)
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) : Prop :=
  Htop.map (TopCat.ofHom f) ≠ 0 →
    ¬ EmbeddedCirclePreimage.HasNullWindingPreimage Hcircle f c

/-- The geometric non-null-winding witness principle is equivalent to the
eliminator form consumed by homological applications.  Besides supplying the
forward adapter, the reverse implication is a non-vacuity check on the new
geometric interface. -/
theorem nonzeroTopMapHasNonNullWinding_iff_detectsTopMap
    {D E : Type*} [Category D] [Category E]
    [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (Hcircle : TopCat ⥤ D) (Htop : TopCat ⥤ E)
    {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) :
    NonzeroTopMapHasNonNullWinding Hcircle Htop f c ↔
      DetectsTopMap Hcircle Htop f c := by
  constructor
  · intro h hnull
    by_contra hne
    exact h hne hnull
  · intro h hne hnull
    exact hne (h hnull)

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
#print axioms ConstructionTargets.TransversePreimageDuality.nonzeroTopMapHasNonNullWinding_iff_detectsTopMap
