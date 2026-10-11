import ConstructionTargets.CoveringDegree

open Set

noncomputable section

namespace ConstructionTargets.T99J01ComponentSheetBounds

open ConstructionTargets.CoveringDegree

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The fiber of a cover at `p e`, restricted to the path component of `e`.
This is the type whose cardinality occurs literally in `t99J01`. -/
abbrev ComponentFiber (p : E → B) (e : E) :=
  {x : E // p x = p e ∧ Joined e x}

/-- A component fiber embeds in the full covering fiber. -/
def componentFiberEmbedding (p : E → B) (e : E) :
    ComponentFiber p e ↪ {x : E // p x = p e} where
  toFun x := ⟨x.1, x.2.1⟩
  inj' x y h := by
    apply Subtype.ext
    exact congrArg (fun z => z.1) h

/-- The chosen point makes its component fiber nonempty. -/
theorem componentFiber_nonempty (p : E → B) (e : E) :
    Nonempty (ComponentFiber p e) :=
  ⟨⟨e, rfl, Joined.refl e⟩⟩

/-- A component of a finite-sheeted cover has a positive number of sheets. -/
theorem componentFiberCard_pos {p : E → B} {n : ℕ}
    (hp : IsKSheetedCover p n) (e : E) :
    0 < Nat.card (ComponentFiber p e) := by
  letI : Finite {x : E // p x = p e} := hp.finite_fiber (p e)
  letI : Finite (ComponentFiber p e) :=
    Finite.of_injective (componentFiberEmbedding p e)
      (componentFiberEmbedding p e).injective
  letI : Nonempty (ComponentFiber p e) := componentFiber_nonempty p e
  exact Finite.card_pos

/-- A component fiber has at most as many points as the full covering fiber. -/
theorem componentFiberCard_le {p : E → B} {n : ℕ}
    (hp : IsKSheetedCover p n) (e : E) :
    Nat.card (ComponentFiber p e) ≤ n := by
  letI : Finite {x : E // p x = p e} := hp.finite_fiber (p e)
  rw [← hp.card_fiber (p e)]
  exact Nat.card_le_card_of_injective (componentFiberEmbedding p e)
    (componentFiberEmbedding p e).injective

#print axioms componentFiber_nonempty
#print axioms componentFiberCard_pos
#print axioms componentFiberCard_le

end ConstructionTargets.T99J01ComponentSheetBounds
