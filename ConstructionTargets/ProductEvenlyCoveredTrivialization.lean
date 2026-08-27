import Mathlib.Topology.Covering.Basic

/-! # Products of evenly covered neighborhoods -/

open Set

noncomputable section

namespace ConstructionTargets.ProductEvenlyCoveredTrivialization

variable {E₁ X₁ E₂ X₂ I J : Type*}
  [TopologicalSpace E₁] [TopologicalSpace X₁]
  [TopologicalSpace E₂] [TopologicalSpace X₂]
  [TopologicalSpace I] [TopologicalSpace J]

def productMap (f : E₁ → X₁) (g : E₂ → X₂) : E₁ × E₂ → X₁ × X₂ :=
  fun p ↦ (f p.1, g p.2)

/-- Pair two local covering trivializations over the product neighborhood. -/
theorem isEvenlyCovered_productMap {f : E₁ → X₁} {g : E₂ → X₂}
    {x : X₁} {y : X₂}
    (hf : IsEvenlyCovered f x I) (hg : IsEvenlyCovered g y J) :
    IsEvenlyCovered (productMap f g) (x, y) (I × J) := by
  rcases hf with ⟨hdiscI, U, hxU, hU, hfU, Hf, hHf⟩
  rcases hg with ⟨hdiscJ, V, hyV, hV, hgV, Hg, hHg⟩
  letI : DiscreteTopology I := hdiscI
  letI : DiscreteTopology J := hdiscJ
  refine ⟨inferInstance, U ×ˢ V, ⟨hxU, hyV⟩, hU.prod hV, ?_, ?_, ?_⟩
  · simpa [productMap] using hfU.prod hgV
  · exact
      { toFun := fun p ↦
          (⟨((Hf ⟨p.1.1, p.2.1⟩).1.1, (Hg ⟨p.1.2, p.2.2⟩).1.1),
             (Hf ⟨p.1.1, p.2.1⟩).1.2, (Hg ⟨p.1.2, p.2.2⟩).1.2⟩,
           ((Hf ⟨p.1.1, p.2.1⟩).2, (Hg ⟨p.1.2, p.2.2⟩).2))
        invFun := fun q ↦
          ⟨((Hf.symm (⟨q.1.1.1, q.1.2.1⟩, q.2.1)).1,
             (Hg.symm (⟨q.1.1.2, q.1.2.2⟩, q.2.2)).1), by
            constructor
            · change f (Hf.symm (⟨q.1.1.1, q.1.2.1⟩, q.2.1)).1 ∈ U
              exact (Hf.symm (⟨q.1.1.1, q.1.2.1⟩, q.2.1)).2
            · change g (Hg.symm (⟨q.1.1.2, q.1.2.2⟩, q.2.2)).1 ∈ V
              exact (Hg.symm (⟨q.1.1.2, q.1.2.2⟩, q.2.2)).2⟩
        left_inv := by
          intro p
          apply Subtype.ext
          exact Prod.ext
            (congrArg Subtype.val (Hf.symm_apply_apply ⟨p.1.1, p.2.1⟩))
            (congrArg Subtype.val (Hg.symm_apply_apply ⟨p.1.2, p.2.2⟩))
        right_inv := by
          intro q
          ext <;> simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
  · intro p
    exact Prod.ext (hHf ⟨p.1.1, p.2.1⟩) (hHg ⟨p.1.2, p.2.2⟩)

/-- The product of the coordinate fibers is the fiber of the product map. -/
def productFiberHomeomorph (f : E₁ → X₁) (g : E₂ → X₂) (x : X₁) (y : X₂) :
    (f ⁻¹' {x}) × (g ⁻¹' {y}) ≃ₜ
      productMap f g ⁻¹' {(x, y)} where
  toFun p := ⟨(p.1.1, p.2.1), by
    change (f p.1.1, g p.2.1) = (x, y)
    exact Prod.ext p.1.2 p.2.2⟩
  invFun p :=
    (⟨p.1.1, by
       have hp : (f p.1.1, g p.1.2) = (x, y) := p.2
       exact congrArg Prod.fst hp⟩,
     ⟨p.1.2, by
       have hp : (f p.1.1, g p.1.2) = (x, y) := p.2
       exact congrArg Prod.snd hp⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Product covering maps, derived from their pointwise evenly-covered
trivializations and the explicit product-fiber homeomorphism. -/
theorem isCoveringMap_productMap {f : E₁ → X₁} {g : E₂ → X₂}
    (hf : IsCoveringMap f) (hg : IsCoveringMap g) :
    IsCoveringMap (productMap f g) := by
  rintro ⟨x, y⟩
  exact (isEvenlyCovered_productMap (hf x) (hg y)).of_fiber_homeomorph
    (productFiberHomeomorph f g x y)

#print axioms isEvenlyCovered_productMap
#print axioms productFiberHomeomorph
#print axioms isCoveringMap_productMap

end ConstructionTargets.ProductEvenlyCoveredTrivialization
