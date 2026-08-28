import Mathlib.Order.Fin.SuccAboveOrderIso
import Mathlib.Data.Finset.Sort

/-!
# Complements of finite order embeddings
-/

open Set
noncomputable section

namespace ConstructionTargets.FinOrderEmbeddingComplement

variable {n m : ℕ}

/-- Codomain indices not occupied by a finite order embedding. -/
def complement (e : Fin (n + 2) ↪o Fin (n + m + 2)) :
    Finset (Fin (n + m + 2)) :=
  Finset.univ \ Finset.univ.image e

@[simp] theorem mem_complement_iff (e : Fin (n + 2) ↪o Fin (n + m + 2))
    (j : Fin (n + m + 2)) :
    j ∈ complement e ↔ j ∉ Set.range e := by
  simp [complement]

theorem card_complement (e : Fin (n + 2) ↪o Fin (n + m + 2)) :
    (complement e).card = m := by
  rw [complement, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ,
    Finset.card_image_iff.mpr e.injective.injOn, Fintype.card_fin]
  omega

/-- Increasing list of the unoccupied codomain indices. -/
def complementList (e : Fin (n + 2) ↪o Fin (n + m + 2)) :
    List (Fin (n + m + 2)) :=
  (complement e).sort (· ≤ ·)

@[simp] theorem length_complementList
    (e : Fin (n + 2) ↪o Fin (n + m + 2)) :
    (complementList e).length = m := by
  simp [complementList, card_complement]

theorem sorted_complementList
    (e : Fin (n + 2) ↪o Fin (n + m + 2)) :
    (complementList e).SortedLE := by
  exact (complement e).pairwise_sort (fun a b ↦ a ≤ b) |>.sortedLE

theorem complement_ne_zero
    (e : Fin (n + 2) ↪o Fin (n + m + 2)) (h0 : e 0 = 0)
    {j} (hj : j ∈ complement e) : j ≠ 0 := by
  intro h
  subst j
  exact (mem_complement_iff e 0).mp hj ⟨0, h0⟩

theorem complement_ne_last
    (e : Fin (n + 2) ↪o Fin (n + m + 2))
    (hlast : e (Fin.last (n + 1)) = Fin.last (n + m + 1))
    {j} (hj : j ∈ complement e) : j ≠ Fin.last (n + m + 1) := by
  intro h
  subst j
  exact (mem_complement_iff e _).mp hj ⟨Fin.last (n + 1), hlast⟩

/-- Removing a chosen complement index leaves a canonical smaller finite
ordinal, via `predAbove`; this is the index transport used by a one-step
extension. -/
def removeComplementOrderIso (j : Fin (n + m + 2)) :
    ↑({j}ᶜ : Finset (Fin (n + m + 2))) ≃o Fin (n + m + 1) :=
  (Fin.succAboveOrderIso j).symm

#print axioms card_complement
#print axioms length_complementList
#print axioms complement_ne_zero
#print axioms complement_ne_last
#print axioms removeComplementOrderIso

end ConstructionTargets.FinOrderEmbeddingComplement
