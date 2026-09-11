import ConstructionTargets.ProductSimplexBalancedAdjacentSwap

namespace ConstructionTargets.ProductSimplexAdjacentPathSwap

open ProductSimplexBalancedWords
open ProductSimplexMaximalPaths
open ProductSimplexWordPathEquivalence
open ProductSimplexBalancedAdjacentSwap

noncomputable section

def adjacentSwapPath {p q n : ℕ} (z : MaximalPath p q)
    (h : n + 1 = p + q) (i : Fin n) : MaximalPath p q :=
  wordPathEquiv p q (balancedAdjacentSwap ((wordPathEquiv p q).symm z) h i)

@[simp] theorem adjacentSwapPath_word {p q n : ℕ} (z : MaximalPath p q)
    (h : n + 1 = p + q) (i : Fin n) :
    (wordPathEquiv p q).symm (adjacentSwapPath z h i) =
      balancedAdjacentSwap ((wordPathEquiv p q).symm z) h i := by
  exact (wordPathEquiv p q).symm_apply_apply _

@[simp] theorem adjacentSwapPath_toWord {p q n : ℕ} (z : MaximalPath p q)
    (h : n + 1 = p + q) (i : Fin n) (j : Fin (p + q)) :
    ((wordPathEquiv p q).symm (adjacentSwapPath z h i)).toWord j =
      (balancedAdjacentSwap ((wordPathEquiv p q).symm z) h i).toWord j := by
  rw [adjacentSwapPath_word]

@[simp] theorem adjacentSwapPath_involutive {p q n : ℕ} (z : MaximalPath p q)
    (h : n + 1 = p + q) (i : Fin n) :
    adjacentSwapPath (adjacentSwapPath z h i) h i = z := by
  apply (wordPathEquiv p q).symm.injective
  rw [adjacentSwapPath_word, adjacentSwapPath_word,
    balancedAdjacentSwap_involutive]

#print axioms adjacentSwapPath_word
#print axioms adjacentSwapPath_toWord
#print axioms adjacentSwapPath_involutive

end

end ConstructionTargets.ProductSimplexAdjacentPathSwap
