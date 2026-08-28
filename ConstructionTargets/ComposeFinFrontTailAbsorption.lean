import ConstructionTargets.ComposeFinAppend

/-!
# Absorbing endpoint transports in dependent front recursion
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ComposeFinFrontTailAbsorption

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.ComposeFinIndexReindex
open ConstructionTargets.ComposeFinAppend

variable {C : Type*} [Category C]

/-- The absorption pattern independently of finite chains. -/
theorem absorb_conjugated_middle {A₀ A₁ B₁ B₂ A₂ Z : C}
    (a : A₀ ⟶ A₁) (e₁ : A₁ ≅ B₁) (t : B₁ ⟶ B₂)
    (e₂ : A₂ ≅ B₂) (b : A₂ ⟶ Z) :
    a ≫ (e₁.hom ≫ t ≫ e₂.inv) ≫ b =
      (a ≫ e₁.hom) ≫ t ≫ (e₂.inv ≫ b) := by
  simp only [Category.assoc]

/-- Reassociate the endpoint transports produced by tail reindexing into the
neighboring prefix and suffix arrows.  The transports remain explicit and
typed throughout. -/
theorem composeFin_front_tail_absorbed {n : ℕ} (A : Fin (n + 3) → C)
    (f : (i : Fin (n + 2)) → A i.castSucc ⟶ A i.succ)
    {Z : C}
    (k : A (Fin.last n).succ.castSucc ⟶ Z) :
    f 0 ≫
          TwoOpenDescentDatum.composeFin
            (A ∘ fun i : Fin (n + 1) ↦ i.succ.castSucc)
            (fun i : Fin n ↦ f i.succ.castSucc) ≫ k =
      (f 0 ≫
          (objectIsoOfIndexEq A
            (succ_castSucc_eq_castSucc_succ 0)).hom) ≫
        TwoOpenDescentDatum.composeFin
          (A ∘ fun i : Fin (n + 1) ↦ i.castSucc.succ)
          (fun i : Fin n ↦ f i.castSucc.succ) ≫
        ((objectIsoOfIndexEq A
            (succ_castSucc_eq_castSucc_succ (Fin.last n))).inv ≫ k) := by
  rw [composeFin_front_tail_reindex A f]
  exact absorb_conjugated_middle _ _ _ _ _

#print axioms composeFin_front_tail_absorbed
#print axioms absorb_conjugated_middle

end ConstructionTargets.ComposeFinFrontTailAbsorption
