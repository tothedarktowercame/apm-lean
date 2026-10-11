import Mathlib

open Set

/-! Transition maps between nested embedded compact intervals. -/

namespace ConstructionTargets.NestedEmbeddingTransition

variable {I X : Type*} [TopologicalSpace I] [TopologicalSpace X]

/-- The coordinate transition from one embedded copy into a larger embedded
copy, defined using the inverse of the latter embedding onto its range. -/
noncomputable def transition (f g : I → X) (hg : Topology.IsEmbedding g)
    (hfg : Set.range f ⊆ Set.range g) : I → I :=
  fun x => hg.toHomeomorph.symm ⟨f x, hfg ⟨x, rfl⟩⟩

theorem g_transition (f g : I → X) (hg : Topology.IsEmbedding g)
    (hfg : Set.range f ⊆ Set.range g) (x : I) :
    g (transition f g hg hfg x) = f x := by
  exact congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply ⟨f x, hfg ⟨x, rfl⟩⟩)

theorem continuous_transition (f g : I → X) (hf : Continuous f)
    (hg : Topology.IsEmbedding g) (hfg : Set.range f ⊆ Set.range g) :
    Continuous (transition f g hg hfg) := by
  exact hg.toHomeomorph.symm.continuous.comp (hf.subtype_mk _)

theorem injective_transition (f g : I → X) (hf : Function.Injective f)
    (hg : Topology.IsEmbedding g) (hfg : Set.range f ⊆ Set.range g) :
    Function.Injective (transition f g hg hfg) := by
  intro x y hxy
  apply hf
  rw [← g_transition f g hg hfg x, ← g_transition f g hg hfg y, hxy]

theorem transition_mem_of_range_subset_image (f g : I → X)
    (hg : Topology.IsEmbedding g) (U : Set I)
    (hfgU : Set.range f ⊆ g '' U) (x : I) :
    transition f g hg (hfgU.trans (image_subset_range g U)) x ∈ U := by
  obtain ⟨y, hyU, hy⟩ := hfgU ⟨x, rfl⟩
  have hgy : g (transition f g hg
      (hfgU.trans (image_subset_range g U)) x) = g y := by
    exact (g_transition f g hg
      (hfgU.trans (image_subset_range g U)) x).trans hy.symm
  exact hg.injective hgy ▸ hyU

end ConstructionTargets.NestedEmbeddingTransition

#print axioms ConstructionTargets.NestedEmbeddingTransition.g_transition
#print axioms ConstructionTargets.NestedEmbeddingTransition.continuous_transition
#print axioms ConstructionTargets.NestedEmbeddingTransition.injective_transition
#print axioms ConstructionTargets.NestedEmbeddingTransition.transition_mem_of_range_subset_image
