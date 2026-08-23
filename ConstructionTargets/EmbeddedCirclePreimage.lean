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
  rcases hcomponents x hx with ⟨γ, hxγ, hγsub, hγzero⟩
  rcases EmbeddedCircleLift.map_component_lift_eq_zero
      F f c hc γ hγsub hγzero with ⟨ℓ, hlift, hℓzero⟩
  exact ⟨γ, ℓ, hxγ, hlift, hℓzero⟩

end ConstructionTargets.EmbeddedCirclePreimage

#print axioms ConstructionTargets.EmbeddedCirclePreimage.exists_component_lift_eq_zero
