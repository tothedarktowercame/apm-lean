import ConstructionTargets.ProductSimplexAdjacentWordInversionCard
import ConstructionTargets.ProductSimplexAdjacentPathSwap

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexAdjacentSwapSignReversal

universe u
open SSet
open ProductSimplexBalancedWords
open ProductSimplexBalancedAdjacentSwap
open ProductSimplexAdjacentWordSwap
open ProductSimplexAdjacentPathSwap
open ProductSimplexMaximalPaths
open ProductSimplexWordPathEquivalence
open ProductSimplexShuffleParity
open ProductSimplexWordInversionPairs
open ProductSimplexAdjacentWordInversionCard
open ProductSimplexInversionCardParity

private theorem wordInversionPairs_card_comp_finCongr {a b : ℕ}
    (h : a = b) (w : Fin b → Bool) :
    (wordInversionPairs (w ∘ finCongr h)).card =
      (wordInversionPairs w).card := by
  subst b
  rfl

private theorem balancedAdjacentSwap_transport {p q n : ℕ}
    (w : BalancedWord p q) (h : n + 1 = p + q) (i : Fin n) :
    (balancedAdjacentSwap w h i).toWord ∘ finCongr h =
      adjacentSwapWord (w.toWord ∘ finCongr h) i := by
  funext j
  change (balancedAdjacentSwap w h i).toWord (finCongr h j) =
    adjacentSwapWord (w.toWord ∘ finCongr h) i j
  rw [balancedAdjacentSwap_toWord_explicit]
  simp [adjacentSwapWord]

private theorem balancedAdjacentSwap_inversion_card {p q n : ℕ}
    (w : BalancedWord p q) (h : n + 1 = p + q) (i : Fin n)
    (hne : w.toWord (finCongr h i.castSucc) ≠
      w.toWord (finCongr h i.succ)) :
    (wordInversionPairs w.toWord).card + 1 =
        (wordInversionPairs (balancedAdjacentSwap w h i).toWord).card ∨
      (wordInversionPairs (balancedAdjacentSwap w h i).toWord).card + 1 =
        (wordInversionPairs w.toWord).card := by
  let wn : Fin (n + 1) → Bool := w.toWord ∘ finCongr h
  have hne' : wn i.castSucc ≠ wn i.succ := hne
  have hc := wordInversionPairs_card_adjacentSwapWord wn i hne'
  dsimp only [wn] at hc
  have hs := wordInversionPairs_card_comp_finCongr h w.toWord
  have ht := wordInversionPairs_card_comp_finCongr h
    (balancedAdjacentSwap w h i).toWord
  rw [balancedAdjacentSwap_transport w h i] at ht
  rcases hc with hc | hc
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem shuffleSign_adjacentSwapPath {p q n : ℕ} (z : MaximalPath.{u} p q)
    (h : n + 1 = p + q) (i : Fin n)
    (hne : ((wordPathEquiv.{u} p q).symm z).toWord (finCongr h i.castSucc) ≠
      ((wordPathEquiv.{u} p q).symm z).toWord (finCongr h i.succ)) :
    shuffleSign (adjacentSwapPath.{u,u} z h i) = -shuffleSign z := by
  let w := (wordPathEquiv.{u} p q).symm z
  have hc := balancedAdjacentSwap_inversion_card w h i hne
  rw [shuffleSign, shuffleSign, inversionPairs_eq_wordInversionPairs,
    inversionPairs_eq_wordInversionPairs, adjacentSwapPath_word]
  exact neg_one_pow_card_eq_neg_of_unit_difference _ _ hc

#print axioms shuffleSign_adjacentSwapPath

end ConstructionTargets.ProductSimplexAdjacentSwapSignReversal
