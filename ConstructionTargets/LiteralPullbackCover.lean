import Mathlib

open Set
noncomputable section
namespace ConstructionTargets.LiteralPullbackCover
variable {E B Y : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]

def Pullback (p : E → B) (f : Y → B) := {q : Y × E // f q.1 = p q.2}
instance (p : E → B) (f : Y → B) : TopologicalSpace (Pullback p f) := inferInstanceAs (TopologicalSpace {q : Y × E // f q.1 = p q.2})
def projection (p : E → B) (f : Y → B) : Pullback p f → Y := fun q => q.1.1

def fiberHomeomorph (p : E → B) (f : Y → B) (y : Y) :
    {q : Pullback p f // projection p f q = y} ≃ₜ {e : E // p e = f y} where
  toFun q := ⟨q.1.1.2, q.1.2.symm.trans (congrArg f q.2)⟩
  invFun e := ⟨⟨(y, e.1), e.2.symm⟩, rfl⟩
  left_inv q := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext q.2.symm rfl
  right_inv e := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [TopologicalSpace B] in
@[simp] theorem fiberHomeomorph_apply (p : E → B) (f : Y → B) (y : Y)
    (q : {q : Pullback p f // projection p f q = y}) :
    (fiberHomeomorph p f y q).1 = q.1.1.2 := rfl

omit [TopologicalSpace B] in
theorem fiber_card (p : E → B) (f : Y → B) (y : Y) :
    Nat.card {q : Pullback p f // projection p f q = y} = Nat.card {e : E // p e = f y} :=
  Nat.card_congr (fiberHomeomorph p f y).toEquiv

theorem evenlyCovered {p : E → B} {f : Y → B} (hf : Continuous f)
    (y : Y) {I : Type*} [TopologicalSpace I] (h : IsEvenlyCovered p (f y) I) :
    IsEvenlyCovered (projection p f) y I := by
  rcases h with ⟨hI, U, hy, hU, hpU, H, hH⟩
  letI : DiscreteTopology I := hI
  have hproj : Continuous (projection p f) := continuous_fst.comp continuous_subtype_val
  refine ⟨inferInstance, f ⁻¹' U, hy, hU.preimage hf,
    (hU.preimage hf).preimage hproj, ?_, ?_⟩
  · exact
      { toFun := fun q => (⟨q.1.1.1, q.2⟩,
          (H ⟨q.1.1.2, by change p q.1.1.2 ∈ U; rw [← q.1.2]; exact q.2⟩).2)
        invFun := fun r => ⟨⟨(r.1.1, (H.symm (⟨f r.1.1, r.1.2⟩, r.2)).1), by
          have hh := hH (H.symm (⟨f r.1.1, r.1.2⟩, r.2))
          simpa using hh⟩, r.1.2⟩
        left_inv := by
          intro q
          dsimp only
          apply Subtype.ext; apply Subtype.ext
          refine Prod.ext ?_ ?_
          · rfl
          have hh := hH ⟨q.1.1.2, by change p q.1.1.2 ∈ U; rw [← q.1.2]; exact q.2⟩
          have he : (⟨f q.1.1.1, q.2⟩, (H ⟨q.1.1.2, by change p q.1.1.2 ∈ U; rw [← q.1.2]; exact q.2⟩).2) =
              H ⟨q.1.1.2, by change p q.1.1.2 ∈ U; rw [← q.1.2]; exact q.2⟩ := by
            refine Prod.ext ?_ ?_
            · exact Subtype.ext (q.1.2.trans hh.symm)
            · rfl
          change (H.symm (⟨f q.1.1.1, q.2⟩, (H ⟨q.1.1.2, by change p q.1.1.2 ∈ U; rw [← q.1.2]; exact q.2⟩).2)).1 = q.1.1.2
          rw [he, H.symm_apply_apply]
        right_inv := by
          intro r
          dsimp only
          refine Prod.ext ?_ ?_
          · rfl
          change (H (H.symm (⟨f r.1.1, r.1.2⟩, r.2))).2 = r.2
          exact congrArg Prod.snd (H.apply_symm_apply (⟨f r.1.1, r.1.2⟩, r.2))
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
  · intro q; rfl

theorem isCoveringMap {p : E → B} {f : Y → B} (hp : IsCoveringMap p)
    (hf : Continuous f) : IsCoveringMap (projection p f) :=
  fun y => (evenlyCovered hf y (hp (f y))).to_isEvenlyCovered_preimage

theorem circle_pullback : IsCoveringMap
    (projection ((↑) : ℝ → AddCircle (1 : ℝ)) (fun z : AddCircle (1 : ℝ) => z + z)) :=
  isCoveringMap (AddCircle.isCoveringMap_coe _) (continuous_id.add continuous_id)

omit [TopologicalSpace B] in
theorem sheet_card (p : E → B) (f : Y → B) (y : Y) (n : ℕ)
    (h : Nat.card {e : E // p e = f y} = n) :
    Nat.card {q : Pullback p f // projection p f q = y} = n :=
  (fiber_card p f y).trans h

theorem empty_disconnected_pullback : IsCoveringMap
    (projection (fun e : Empty => Empty.elim e : Empty → Unit) (fun _ : Bool => ())) :=
  isCoveringMap (IsCoveringMap.of_discreteTopology _) continuous_const

theorem empty_fiber_card (y : Bool) :
    Nat.card {q : Pullback (fun e : Empty => Empty.elim e : Empty → Unit)
      (fun _ : Bool => ()) // projection _ _ q = y} = 0 := by
  rw [fiber_card]
  simp

#print axioms fiberHomeomorph_apply
#print axioms sheet_card
#print axioms empty_disconnected_pullback
#print axioms empty_fiber_card
#print axioms fiberHomeomorph
#print axioms fiber_card
#print axioms evenlyCovered
#print axioms isCoveringMap
#print axioms circle_pullback
end ConstructionTargets.LiteralPullbackCover
