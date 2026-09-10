import ConstructionTargets.ProductSimplexWordPathEquivalence

namespace ConstructionTargets.ProductSimplexAdjacentWordSwap

/-- Exchange the two positions adjacent to the cut indexed by `i`. -/
def adjacentSwapWord {n : ℕ} (w : Fin (n + 1) → Bool) (i : Fin n) :
    Fin (n + 1) → Bool :=
  w ∘ Equiv.swap i.castSucc i.succ

@[simp] theorem adjacentSwapWord_left {n : ℕ} (w : Fin (n + 1) → Bool) (i : Fin n) :
    adjacentSwapWord w i i.castSucc = w i.succ := by
  simp [adjacentSwapWord]

@[simp] theorem adjacentSwapWord_right {n : ℕ} (w : Fin (n + 1) → Bool) (i : Fin n) :
    adjacentSwapWord w i i.succ = w i.castSucc := by
  simp [adjacentSwapWord]

@[simp] theorem adjacentSwapWord_of_ne {n : ℕ} (w : Fin (n + 1) → Bool) (i : Fin n)
    (j : Fin (n + 1)) (hj₁ : j ≠ i.castSucc) (hj₂ : j ≠ i.succ) :
    adjacentSwapWord w i j = w j := by
  simp [adjacentSwapWord, Equiv.swap_apply_def, hj₁, hj₂]

@[simp] theorem adjacentSwapWord_involutive {n : ℕ} (w : Fin (n + 1) → Bool)
    (i : Fin n) :
    adjacentSwapWord (adjacentSwapWord w i) i = w := by
  funext j
  simp [adjacentSwapWord]

#print axioms adjacentSwapWord_left
#print axioms adjacentSwapWord_right
#print axioms adjacentSwapWord_of_ne
#print axioms adjacentSwapWord_involutive

end ConstructionTargets.ProductSimplexAdjacentWordSwap
