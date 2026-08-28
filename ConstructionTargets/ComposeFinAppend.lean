import ConstructionTargets.ComposeFinIndexReindex

/-!
# Front recursion for dependent finite categorical folds
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ComposeFinAppend

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.ComposeFinIndexReindex

variable {C : Type*} [Category C]

/-- Evaluating a dependent arrow family at propositionally equal indices
produces the expected endpoint conjugation. -/
theorem dependentArrow_conjugation {n : ℕ} (A : Fin (n + 2) → C)
    (f : (i : Fin (n + 1)) → A i.castSucc ⟶ A i.succ)
    {a b : Fin (n + 1)} (h : a = b) :
    f a = eqToHom (congrArg A (congrArg Fin.castSucc h)) ≫ f b ≫
      eqToHom (congrArg A (congrArg Fin.succ h)).symm := by
  subst b
  simp

/-- The exact proof-carrying comparison between the two tail-chain
representations arising in front recursion. Outer endpoint transports are
retained; they are not definitionally identities. -/
theorem composeFin_front_tail_reindex {n : ℕ} (A : Fin (n + 3) → C)
    (f : (i : Fin (n + 2)) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin
        (A ∘ fun i : Fin (n + 1) ↦ i.succ.castSucc)
        (fun i : Fin n ↦ f i.succ.castSucc) =
      (objectIsoOfIndexEq A (succ_castSucc_eq_castSucc_succ 0)).hom ≫
        TwoOpenDescentDatum.composeFin
          (A ∘ fun i : Fin (n + 1) ↦ i.castSucc.succ)
          (fun i : Fin n ↦ f i.castSucc.succ) ≫
        (objectIsoOfIndexEq A
          (succ_castSucc_eq_castSucc_succ (Fin.last n))).inv := by
  apply composeFin_reindex_of_index_eq A
    (fun i : Fin (n + 1) ↦ i.castSucc.succ)
    (fun i : Fin (n + 1) ↦ i.succ.castSucc)
    (fun i ↦ succ_castSucc_eq_castSucc_succ i)
    (fun i : Fin n ↦ f i.castSucc.succ)
    (fun i : Fin n ↦ f i.succ.castSucc)
  intro i
  simpa [objectIsoOfIndexEq] using dependentArrow_conjugation A f
    (succ_castSucc_eq_castSucc_succ i)

#print axioms dependentArrow_conjugation
#print axioms composeFin_front_tail_reindex

end ConstructionTargets.ComposeFinAppend
