import ConstructionTargets.PathSubdivisionConcatenation

/-!
# Conjugation of finite dependent categorical folds
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ComposeFinConjugation

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent

variable {C : Type*} [Category C]

/-- Pointwise conjugation of every arrow in a dependent finite chain
conjugates its total ordered composite only at the two outer endpoints. -/
theorem composeFin_conjugation {n : ℕ} (A B : Fin (n + 1) → C)
    (f : (i : Fin n) → A i.castSucc ⟶ A i.succ)
    (g : (i : Fin n) → B i.castSucc ⟶ B i.succ)
    (e : (i : Fin (n + 1)) → B i ≅ A i)
    (h : ∀ i, g i = (e i.castSucc).hom ≫ f i ≫ (e i.succ).inv) :
    TwoOpenDescentDatum.composeFin B g =
      (e 0).hom ≫ TwoOpenDescentDatum.composeFin A f ≫
        (e (Fin.last n)).inv := by
  induction n with
  | zero =>
      simp only [TwoOpenDescentDatum.composeFin_zero]
      simp
  | succ n ih =>
      rw [TwoOpenDescentDatum.composeFin_succ,
        TwoOpenDescentDatum.composeFin_succ]
      have hp := ih (A := A ∘ Fin.castSucc) (B := B ∘ Fin.castSucc)
        (f := fun i ↦ f i.castSucc) (g := fun i ↦ g i.castSucc)
        (e := fun i ↦ e i.castSucc) (fun i ↦ h i.castSucc)
      rw [hp, h (Fin.last n)]
      simp only [Function.comp_apply, Category.assoc]
      rw [Iso.inv_hom_id_assoc]
      simpa only [Category.assoc, Fin.castSucc_zero, Fin.succ_last]

#print axioms composeFin_conjugation

end ConstructionTargets.ComposeFinConjugation
