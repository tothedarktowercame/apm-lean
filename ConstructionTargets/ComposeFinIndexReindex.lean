import ConstructionTargets.ComposeFinConjugation

/-!
# Proof-carrying reindexing of dependent finite chains
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ComposeFinIndexReindex

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.ComposeFinConjugation

variable {C : Type*} [Category C]

/-- An index equality induces the correctly typed object isomorphism. -/
def objectIsoOfIndexEq {ι : Type*} (O : ι → C) {a b : ι} (h : a = b) :
    O a ≅ O b := eqToIso (congrArg O h)

/-- Compare two finite dependent chains whose vertex-index maps agree
pointwise.  Arrow compatibility is stated only after the induced object
isomorphisms have aligned its source and target types. -/
theorem composeFin_reindex_of_index_eq {ι : Type*} {n : ℕ}
    (O : ι → C) (r s : Fin (n + 1) → ι)
    (hr : ∀ i, s i = r i)
    (f : (i : Fin n) → O (r i.castSucc) ⟶ O (r i.succ))
    (g : (i : Fin n) → O (s i.castSucc) ⟶ O (s i.succ))
    (h : ∀ i, g i =
      (objectIsoOfIndexEq O (hr i.castSucc)).hom ≫ f i ≫
        (objectIsoOfIndexEq O (hr i.succ)).inv) :
    TwoOpenDescentDatum.composeFin (O ∘ s) g =
      (objectIsoOfIndexEq O (hr 0)).hom ≫
        TwoOpenDescentDatum.composeFin (O ∘ r) f ≫
        (objectIsoOfIndexEq O (hr (Fin.last n))).inv := by
  exact composeFin_conjugation (O ∘ r) (O ∘ s) f g
    (fun i ↦ objectIsoOfIndexEq O (hr i)) h

/-- The front-recursion indices that cannot safely be rewritten underneath a
dependent arrow family are nevertheless propositionally equal. -/
theorem succ_castSucc_eq_castSucc_succ {n : ℕ} (i : Fin n) :
    i.succ.castSucc = i.castSucc.succ := by
  apply Fin.ext
  rfl

/-- The exact equality above produces a typed object isomorphism, without
rewriting an arrow whose type depends on the index. -/
def frontRecursionObjectIso {n : ℕ} (O : Fin (n + 2) → C) (i : Fin n) :
    O i.succ.castSucc ≅ O i.castSucc.succ :=
  objectIsoOfIndexEq O (succ_castSucc_eq_castSucc_succ i)

@[simp] theorem frontRecursionObjectIso_hom {n : ℕ}
    (O : Fin (n + 2) → C) (i : Fin n) :
    (frontRecursionObjectIso O i).hom =
      eqToHom (congrArg O (succ_castSucc_eq_castSucc_succ i)) := rfl

#print axioms composeFin_reindex_of_index_eq
#print axioms succ_castSucc_eq_castSucc_succ
#print axioms frontRecursionObjectIso_hom

end ConstructionTargets.ComposeFinIndexReindex
