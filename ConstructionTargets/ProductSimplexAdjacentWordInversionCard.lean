import ConstructionTargets.ProductSimplexWordInversionPairs

namespace ConstructionTargets.ProductSimplexAdjacentWordInversionCard

open ProductSimplexAdjacentWordSwap
open ProductSimplexWordInversionPairs

private def swapPair {n : ℕ} (i : Fin n)
    (x : Fin (n + 1) × Fin (n + 1)) : Fin (n + 1) × Fin (n + 1) :=
  (Equiv.swap i.castSucc i.succ x.1, Equiv.swap i.castSucc i.succ x.2)

private theorem swap_order_of_ne {n : ℕ} (i : Fin n)
    {x y : Fin (n + 1)} (hxy : x < y)
    (hne : (x, y) ≠ (i.castSucc, i.succ)) :
    Equiv.swap i.castSucc i.succ x < Equiv.swap i.castSucc i.succ y := by
  change (Equiv.swap i.castSucc i.succ x).val <
    (Equiv.swap i.castSucc i.succ y).val
  change x.val < y.val at hxy
  simp only [Equiv.swap_apply_def]
  split_ifs with hxa hxb hya hyb <;> simp_all [Fin.ext_iff] <;> omega

private theorem swapPair_ne_special {n : ℕ} (i : Fin n)
    {x : Fin (n + 1) × Fin (n + 1)} (hxy : x.1 < x.2) :
    swapPair i x ≠ (i.castSucc, i.succ) := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have h1' := congrArg (Equiv.swap i.castSucc i.succ) h1
  have h2' := congrArg (Equiv.swap i.castSucc i.succ) h2
  simp [swapPair] at h1' h2'
  have hx1 : x.1.val = i.val + 1 := congrArg Fin.val h1'
  have hx2 : x.2.val = i.val := congrArg Fin.val h2'
  omega

private theorem erased_card_eq {n : ℕ} (w : Fin (n + 1) → Bool) (i : Fin n) :
    ((wordInversionPairs w).erase (i.castSucc, i.succ)).card =
      ((wordInversionPairs (adjacentSwapWord w i)).erase
        (i.castSucc, i.succ)).card := by
  classical
  apply Finset.card_bij (fun x _ => swapPair i x)
  · intro x hx
    simp only [Finset.mem_erase, wordInversionPairs, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx ⊢
    refine ⟨swapPair_ne_special i hx.2.1, swap_order_of_ne i hx.2.1 ?_, ?_, ?_⟩
    · exact fun h => hx.1 (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    · simpa [swapPair, adjacentSwapWord] using hx.2.2.1
    · simpa [swapPair, adjacentSwapWord] using hx.2.2.2
  · intro a ha b hb hab
    apply Prod.ext <;> simp only [swapPair] at hab ⊢
    · exact (Equiv.swap i.castSucc i.succ).injective (congrArg Prod.fst hab)
    · exact (Equiv.swap i.castSucc i.succ).injective (congrArg Prod.snd hab)
  · intro y hy
    refine ⟨swapPair i y, ?_, ?_⟩
    · simp only [Finset.mem_erase, wordInversionPairs, Finset.mem_filter,
        Finset.mem_univ, true_and] at hy ⊢
      refine ⟨swapPair_ne_special i hy.2.1, swap_order_of_ne i hy.2.1 ?_, ?_, ?_⟩
      · exact fun h => hy.1 (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
      · simpa [swapPair, adjacentSwapWord] using hy.2.2.1
      · simpa [swapPair, adjacentSwapWord] using hy.2.2.2
    · simp [swapPair]

theorem wordInversionPairs_card_adjacentSwapWord {n : ℕ}
    (w : Fin (n + 1) → Bool) (i : Fin n)
    (hne : w i.castSucc ≠ w i.succ) :
    (wordInversionPairs w).card + 1 =
        (wordInversionPairs (adjacentSwapWord w i)).card ∨
      (wordInversionPairs (adjacentSwapWord w i)).card + 1 =
        (wordInversionPairs w).card := by
  classical
  have hc := erased_card_eq w i
  cases ha : w i.castSucc <;> cases hb : w i.succ
  · exact False.elim (hne (ha.trans hb.symm))
  · right
    have hs : (i.castSucc, i.succ) ∈ wordInversionPairs w := by
      simp [wordInversionPairs, ha, hb]
    have ht : (i.castSucc, i.succ) ∉ wordInversionPairs (adjacentSwapWord w i) := by
      simp [wordInversionPairs, ha, hb]
    rw [Finset.erase_eq_of_notMem ht] at hc
    have := Finset.card_erase_add_one hs
    omega
  · left
    have hs : (i.castSucc, i.succ) ∉ wordInversionPairs w := by
      simp [wordInversionPairs, ha, hb]
    have ht : (i.castSucc, i.succ) ∈ wordInversionPairs (adjacentSwapWord w i) := by
      simp [wordInversionPairs, ha, hb]
    rw [Finset.erase_eq_of_notMem hs] at hc
    have := Finset.card_erase_add_one ht
    omega
  · exact False.elim (hne (ha.trans hb.symm))

#print axioms wordInversionPairs_card_adjacentSwapWord

end ConstructionTargets.ProductSimplexAdjacentWordInversionCard
