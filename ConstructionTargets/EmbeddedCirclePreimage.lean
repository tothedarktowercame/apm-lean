import ConstructionTargets.EmbeddedCircleLift

/-!
# Homologically trivial parametrizations of embedded-circle preimages

This module packages the reusable categorical part of a transverse-preimage
argument.  Geometry may supply a homologically trivial circle through each
point of the inverse image.  If the target circle is detected by a
monomorphism under a functor from `TopCat`, each such circle admits a lift to
the target circle and the lifted map is also sent to zero.

No manifold or transversality API is needed for this step: those hypotheses
belong to the producer of the component parametrizations.
-/

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.EmbeddedCirclePreimage

/-- The reusable output of an embedded-circle preimage calculation: every
point of the preimage lies on a circle contained in that preimage, the circle
map factors through the embedded target circle, and the resulting winding map
is killed by `F`.

This packages the exact interface expected by geometric intersection or
Poincare-duality arguments, without committing those arguments to a particular
construction of inverse-image components. -/
def HasNullWindingPreimage
    {D : Type*} [Category D] [Limits.HasZeroMorphisms D]
    (F : Functor TopCat D) {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) : Prop :=
  ∀ x ∈ f ⁻¹' range c,
    ∃ γ : C(Circle, X), ∃ ℓ : C(Circle, Circle),
      x ∈ range γ ∧ range γ ⊆ f ⁻¹' range c ∧
        c.comp ℓ = f.comp γ ∧ F.map (TopCat.ofHom ℓ) = 0

/-- Upgrade pointwise homologically trivial circle parametrizations in an
embedded-circle preimage to parametrizations equipped with a homologically
trivial lift, while retaining the geometric fact that the parametrizing
circle stays in the inverse image.  The retained containment is needed by
downstream geometric arguments (for example, to identify or orient the
inverse-image component), whereas `exists_component_lift_eq_zero` below is
the projection suited to purely homological consumers. -/
theorem exists_component_lift_eq_zero_and_range
    {D : Type*} [Category D] [Limits.HasZeroMorphisms D]
    (F : TopCat ⥤ D) {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    [Mono (F.map (TopCat.ofHom c))]
    (hcomponents : ∀ x ∈ f ⁻¹' range c,
      ∃ γ : C(Circle, X), x ∈ range γ ∧
        range γ ⊆ f ⁻¹' range c ∧ F.map (TopCat.ofHom γ) = 0) :
    ∀ x ∈ f ⁻¹' range c,
      ∃ γ : C(Circle, X), ∃ ℓ : C(Circle, Circle),
        x ∈ range γ ∧ range γ ⊆ f ⁻¹' range c ∧
          c.comp ℓ = f.comp γ ∧ F.map (TopCat.ofHom ℓ) = 0 := by
  intro x hx
  rcases hcomponents x hx with ⟨γ, hxγ, hγsub, hγzero⟩
  rcases EmbeddedCircleLift.map_component_lift_eq_zero
      F f c hc γ hγsub hγzero with ⟨ℓ, hlift, hℓzero⟩
  exact ⟨γ, ℓ, hxγ, hγsub, hlift, hℓzero⟩

/-- Pointwise homological triviality of circles covering an embedded-circle
preimage implies the packaged null-winding preimage condition. -/
theorem hasNullWindingPreimage_of_components
    {D : Type*} [Category D] [Limits.HasZeroMorphisms D]
    (F : Functor TopCat D) {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    [Mono (F.map (TopCat.ofHom c))]
    (hcomponents : ∀ x ∈ f ⁻¹' range c,
      ∃ γ : C(Circle, X), x ∈ range γ ∧
        range γ ⊆ f ⁻¹' range c ∧ F.map (TopCat.ofHom γ) = 0) :
    HasNullWindingPreimage F f c :=
  exists_component_lift_eq_zero_and_range F f c hc hcomponents

/-- Upgrade pointwise homologically trivial circle parametrizations in an
embedded-circle preimage to parametrizations equipped with a homologically
trivial lift to the target circle. -/
theorem exists_component_lift_eq_zero
    {D : Type*} [Category D] [Limits.HasZeroMorphisms D]
    (F : TopCat ⥤ D) {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    [Mono (F.map (TopCat.ofHom c))]
    (hcomponents : ∀ x ∈ f ⁻¹' range c,
      ∃ γ : C(Circle, X), x ∈ range γ ∧
        range γ ⊆ f ⁻¹' range c ∧ F.map (TopCat.ofHom γ) = 0) :
    ∀ x ∈ f ⁻¹' range c,
      ∃ γ : C(Circle, X), ∃ ℓ : C(Circle, Circle),
        x ∈ range γ ∧ c.comp ℓ = f.comp γ ∧
          F.map (TopCat.ofHom ℓ) = 0 := by
  intro x hx
  rcases exists_component_lift_eq_zero_and_range F f c hc hcomponents x hx with
    ⟨γ, ℓ, hxγ, _hγsub, hlift, hℓzero⟩
  exact ⟨γ, ℓ, hxγ, hlift, hℓzero⟩

end ConstructionTargets.EmbeddedCirclePreimage

#print axioms ConstructionTargets.EmbeddedCirclePreimage.exists_component_lift_eq_zero
#print axioms ConstructionTargets.EmbeddedCirclePreimage.exists_component_lift_eq_zero_and_range
#print axioms ConstructionTargets.EmbeddedCirclePreimage.hasNullWindingPreimage_of_components
