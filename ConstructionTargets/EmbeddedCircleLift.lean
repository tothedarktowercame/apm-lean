import Mathlib

/-!
# Lifting through an embedded circle

This module packages a presentation-independent step used when studying
inverse images of embedded circles.  A map landing in an embedded circle has
a continuous lift to the circle.  For any functor out of `TopCat`, if a circle
inclusion is sent to a monomorphism, functoriality then detects vanishing of
the lifted map.
-/

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.EmbeddedCircleLift

/-- A continuous map whose image is contained in an embedded circle lifts
continuously to that circle. -/
def liftToCircle {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hfc : range f ⊆ range c) : C(X, Circle) :=
  (⟨hc.toHomeomorph.symm, hc.toHomeomorph.symm.continuous⟩ :
      C(range c, Circle)).comp
    ⟨fun x => ⟨f x, hfc (mem_range_self x)⟩, f.continuous.subtype_mk _⟩

@[simp] theorem comp_liftToCircle {X S : Type} [TopologicalSpace X]
    [TopologicalSpace S] (f : C(X, S)) (c : C(Circle, S))
    (hc : Topology.IsEmbedding c) (hfc : range f ⊆ range c) :
    c.comp (liftToCircle f c hc hfc) = f := by
  ext x
  change ↑(hc.toHomeomorph (hc.toHomeomorph.symm ⟨f x, hfc (mem_range_self x)⟩)) = f x
  rw [Homeomorph.apply_symm_apply]

/-- Functoriality expressed for continuous maps, avoiding repeated coercion
bookkeeping at consumers. -/
theorem map_comp {D : Type*} [Category D] (F : TopCat ⥤ D)
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    F.map (TopCat.ofHom (g.comp f)) =
      F.map (TopCat.ofHom f) ≫ F.map (TopCat.ofHom g) := by
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g by rfl]
  exact F.map_comp _ _

/-- If an embedded circle is detected monomorphically by a functor, then any
map into that circle whose composite is functorially zero is itself zero. -/
theorem map_lift_eq_zero {D : Type*} [Category D] [Limits.HasZeroMorphisms D]
    (F : TopCat ⥤ D) {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X, S)) (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hfc : range f ⊆ range c) [Mono (F.map (TopCat.ofHom c))]
    (hf : F.map (TopCat.ofHom f) = 0) :
    F.map (TopCat.ofHom (liftToCircle f c hc hfc)) = 0 := by
  rw [← cancel_mono (F.map (TopCat.ofHom c))]
  rw [← map_comp, comp_liftToCircle, hf]
  simp

/-- Pointwise inverse-image form of `map_lift_eq_zero`.  This is suited to a
component parametrization `γ` whose range lies in `f ⁻¹' range c`. -/
theorem map_component_lift_eq_zero {D : Type*} [Category D]
    [Limits.HasZeroMorphisms D] (F : TopCat ⥤ D)
    {S : Type} [TopologicalSpace S] (f : C(S, S))
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    [Mono (F.map (TopCat.ofHom c))] (γ : C(Circle, S))
    (hγ : range γ ⊆ f ⁻¹' range c)
    (hzero : F.map (TopCat.ofHom γ) = 0) :
    ∃ ℓ : C(Circle, Circle), c.comp ℓ = f.comp γ ∧
      F.map (TopCat.ofHom ℓ) = 0 := by
  have hlands : range (f.comp γ) ⊆ range c := by
    rintro _ ⟨z, rfl⟩
    exact hγ (mem_range_self z)
  let ℓ := liftToCircle (f.comp γ) c hc hlands
  refine ⟨ℓ, comp_liftToCircle (f.comp γ) c hc hlands, ?_⟩
  apply map_lift_eq_zero F (f.comp γ) c hc hlands
  rw [map_comp, hzero]
  simp

end ConstructionTargets.EmbeddedCircleLift
