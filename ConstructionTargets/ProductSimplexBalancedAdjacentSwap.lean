import ConstructionTargets.ProductSimplexAdjacentWordSwap

namespace ConstructionTargets.ProductSimplexBalancedAdjacentSwap

open ProductSimplexWordPrefixCounts
open ProductSimplexBalancedWords
open ProductSimplexAdjacentWordSwap

private theorem card_filter_comp_equiv {m : ℕ} (w : Fin m → Bool)
    (e : Equiv.Perm (Fin m)) (b : Bool) :
    (Finset.univ.filter fun j => w (e j) = b).card =
      (Finset.univ.filter fun j => w j = b).card := by
  classical
  apply Finset.card_bij (fun j _ => e j)
  · intro j hj
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
  · intro a _ b _ hab
    exact e.injective hab
  · intro j hj
    refine ⟨e.symm j, ?_, ?_⟩
    · simpa using hj
    · simp

private def adjacentPerm {p q n : ℕ} (h : n + 1 = p + q) (i : Fin n) :
    Equiv.Perm (Fin (p + q)) :=
  (finCongr h.symm).trans ((Equiv.swap i.castSucc i.succ).trans (finCongr h))

private theorem balancedWord_ext {p q : ℕ} {x y : BalancedWord p q}
    (h : x.toWord = y.toWord) : x = y := by
  cases x with
  | mk x hx hy =>
    cases y with
    | mk y hx' hy' =>
      simp only at h
      cases h
      rfl

theorem horizontalCount_adjacentSwapWord_last {n : ℕ} (w : Fin (n + 1) → Bool)
    (i : Fin n) :
    horizontalCount (adjacentSwapWord w i) (Fin.last (n + 1)) =
      horizontalCount w (Fin.last (n + 1)) := by
  rw [horizontalCount_last_eq_card_filter, horizontalCount_last_eq_card_filter]
  exact card_filter_comp_equiv w (Equiv.swap i.castSucc i.succ) true

theorem verticalCount_adjacentSwapWord_last {n : ℕ} (w : Fin (n + 1) → Bool)
    (i : Fin n) :
    verticalCount (adjacentSwapWord w i) (Fin.last (n + 1)) =
      verticalCount w (Fin.last (n + 1)) := by
  rw [verticalCount_last_eq_card_filter, verticalCount_last_eq_card_filter]
  exact card_filter_comp_equiv w (Equiv.swap i.castSucc i.succ) false

def balancedAdjacentSwap {p q n : ℕ} (w : BalancedWord p q)
    (h : n + 1 = p + q) (i : Fin n) : BalancedWord p q where
  toWord j := w.toWord (adjacentPerm h i j)
  horizontal_total := by
    rw [horizontalCount_last_eq_card_filter]
    rw [card_filter_comp_equiv w.toWord (adjacentPerm h i) true]
    rw [← horizontalCount_last_eq_card_filter]
    exact w.horizontal_total
  vertical_total := by
    rw [verticalCount_last_eq_card_filter]
    rw [card_filter_comp_equiv w.toWord (adjacentPerm h i) false]
    rw [← verticalCount_last_eq_card_filter]
    exact w.vertical_total

@[simp] theorem balancedAdjacentSwap_toWord {p q n : ℕ} (w : BalancedWord p q)
    (h : n + 1 = p + q) (i : Fin n) (j : Fin (p + q)) :
    (balancedAdjacentSwap w h i).toWord j = w.toWord (adjacentPerm h i j) := rfl

@[simp] theorem balancedAdjacentSwap_involutive {p q n : ℕ}
    (w : BalancedWord p q) (h : n + 1 = p + q) (i : Fin n) :
    balancedAdjacentSwap (balancedAdjacentSwap w h i) h i = w := by
  apply balancedWord_ext
  funext j
  simp [balancedAdjacentSwap, adjacentPerm]

/-- Public coordinate formula for the transported adjacent swap. -/
theorem balancedAdjacentSwap_toWord_explicit {p q n : ℕ} (w : BalancedWord p q)
    (h : n + 1 = p + q) (i : Fin n) (j : Fin (p + q)) :
    (balancedAdjacentSwap w h i).toWord j =
      w.toWord (finCongr h ((Equiv.swap i.castSucc i.succ) (finCongr h.symm j))) := by
  rfl

@[simp] theorem balancedAdjacentSwap_left {p q n : ℕ} (w : BalancedWord p q)
    (h : n + 1 = p + q) (i : Fin n) :
    (balancedAdjacentSwap w h i).toWord (finCongr h i.castSucc) =
      w.toWord (finCongr h i.succ) := by
  rw [balancedAdjacentSwap_toWord_explicit]
  simp

@[simp] theorem balancedAdjacentSwap_right {p q n : ℕ} (w : BalancedWord p q)
    (h : n + 1 = p + q) (i : Fin n) :
    (balancedAdjacentSwap w h i).toWord (finCongr h i.succ) =
      w.toWord (finCongr h i.castSucc) := by
  rw [balancedAdjacentSwap_toWord_explicit]
  simp

@[simp] theorem balancedAdjacentSwap_of_ne {p q n : ℕ} (w : BalancedWord p q)
    (h : n + 1 = p + q) (i : Fin n) (j : Fin (n + 1))
    (hj₁ : j ≠ i.castSucc) (hj₂ : j ≠ i.succ) :
    (balancedAdjacentSwap w h i).toWord (finCongr h j) =
      w.toWord (finCongr h j) := by
  rw [balancedAdjacentSwap_toWord_explicit]
  simp [Equiv.swap_apply_def, hj₁, hj₂]

#print axioms balancedAdjacentSwap_toWord_explicit
#print axioms balancedAdjacentSwap_left
#print axioms balancedAdjacentSwap_right
#print axioms balancedAdjacentSwap_of_ne
#print axioms horizontalCount_adjacentSwapWord_last
#print axioms verticalCount_adjacentSwapWord_last
#print axioms balancedAdjacentSwap_toWord
#print axioms balancedAdjacentSwap_involutive

end ConstructionTargets.ProductSimplexBalancedAdjacentSwap
