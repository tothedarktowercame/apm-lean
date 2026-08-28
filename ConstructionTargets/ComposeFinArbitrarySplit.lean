import ConstructionTargets.ComposeFinFrontTailAbsorption

/-!
# Recursive splitting of dependent finite categorical composites
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ComposeFinArbitrarySplit

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.ComposeFinFrontTailAbsorption

variable {C : Type*} [Category C]

/-- A composite with at least two arrows splits off its final two arrows.
All restrictions use structural `Fin.castSucc` maps, so no dependent arrow
family is rewritten through an arithmetic equality. -/
theorem composeFin_dropLast_two {n : ℕ} (A : Fin (n + 3) → C)
    (f : (i : Fin (n + 2)) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin A f =
      (TwoOpenDescentDatum.composeFin
          (A ∘ Fin.castSucc ∘ Fin.castSucc)
          (fun i : Fin n ↦ f i.castSucc.castSucc) ≫
        f (Fin.last n).castSucc) ≫
        f (Fin.last (n + 1)) := by
  rw [TwoOpenDescentDatum.composeFin_succ,
    TwoOpenDescentDatum.composeFin_succ]
  simp only [Function.comp_def]
  congr 1

#print axioms composeFin_dropLast_two

end ConstructionTargets.ComposeFinArbitrarySplit
