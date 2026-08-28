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

/-- Reindex vertices across an equality of chain lengths. -/
def castChainVertex {n m : ℕ} (h : n = m) : Fin (m + 1) → Fin (n + 1) :=
  Fin.cast (congrArg (· + 1) h).symm

/-- Reindex segments across an equality of chain lengths. -/
def castChainSegment {n m : ℕ} (h : n = m) : Fin m → Fin n :=
  Fin.cast h.symm

theorem castChainSegment_castSucc {n m : ℕ} (h : n = m) (i : Fin m) :
    (castChainSegment h i).castSucc = castChainVertex h i.castSucc := by
  subst m
  apply Fin.ext
  rfl

theorem castChainSegment_succ {n m : ℕ} (h : n = m) (i : Fin m) :
    (castChainSegment h i).succ = castChainVertex h i.succ := by
  subst m
  apply Fin.ext
  rfl

/-- Compare a dependent finite chain with a presentation whose length is only
propositionally equal. The caller supplies arrows after the `Fin.cast`
endpoints have been aligned; only the first and last object transports remain
in the total fold. -/
theorem composeFin_cast_reindex {n m : ℕ} (h : n = m)
    (A : Fin (n + 1) → C)
    (f : (i : Fin n) → A i.castSucc ⟶ A i.succ)
    (g : (i : Fin m) →
      A (castChainVertex h i.castSucc) ⟶ A (castChainVertex h i.succ))
    (hg : ∀ i, g i =
      (objectIsoOfIndexEq A (castChainSegment_castSucc h i)).inv ≫
        f (castChainSegment h i) ≫
        (objectIsoOfIndexEq A (castChainSegment_succ h i)).hom) :
    TwoOpenDescentDatum.composeFin (A ∘ castChainVertex h) g =
      (objectIsoOfIndexEq A
        (show castChainVertex h 0 = 0 by
          subst m
          apply Fin.ext
          rfl)).hom ≫
      TwoOpenDescentDatum.composeFin A f ≫
      (objectIsoOfIndexEq A
        (show castChainVertex h (Fin.last m) = Fin.last n by
          subst m
          apply Fin.ext
          rfl)).inv := by
  subst m
  apply composeFin_reindex_of_index_eq A id (castChainVertex rfl)
    (fun i => by apply Fin.ext; rfl) f g
  intro i
  simpa [castChainSegment, castChainVertex] using hg i

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
#print axioms castChainSegment_castSucc
#print axioms castChainSegment_succ
#print axioms composeFin_cast_reindex
#print axioms succ_castSucc_eq_castSucc_succ
#print axioms frontRecursionObjectIso_hom

end ConstructionTargets.ComposeFinIndexReindex
