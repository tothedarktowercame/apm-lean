import ConstructionTargets.ProductSimplexPathEndpoints

namespace ConstructionTargets.ProductSimplexWordPrefixCounts

private def wordPrefix {n : ℕ} (i : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun k => k.val < i.val

private theorem wordPrefix_mono {n : ℕ} {i j : Fin (n + 1)} (hij : i ≤ j) :
    wordPrefix i ⊆ wordPrefix j := by
  intro k hk
  simp only [wordPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact lt_of_lt_of_le hk hij

private theorem wordPrefix_succ {n : ℕ} (i : Fin n) :
    wordPrefix i.succ = insert i (wordPrefix i.castSucc) := by
  ext k
  simp only [wordPrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  change k.val < i.val + 1 ↔ k = i ∨ k.val < i.val
  constructor
  · intro hki
    by_cases h : k = i
    · exact Or.inl h
    · right
      have hval : k.val ≠ i.val := fun hval => h (Fin.ext hval)
      omega
  · rintro (rfl | hki)
    · omega
    · omega

/-- Number of horizontal letters strictly before position `i`. -/
def horizontalCount {n : ℕ} (w : Fin n → Bool) (i : Fin (n + 1)) : ℕ :=
  ((wordPrefix i).filter fun k => w k = true).card

/-- Number of vertical letters strictly before position `i`. -/
def verticalCount {n : ℕ} (w : Fin n → Bool) (i : Fin (n + 1)) : ℕ :=
  ((wordPrefix i).filter fun k => w k = false).card

theorem horizontalCount_add_verticalCount {n : ℕ} (w : Fin n → Bool)
    (i : Fin (n + 1)) : horizontalCount w i + verticalCount w i = i := by
  classical
  unfold horizontalCount verticalCount
  have hf : ((wordPrefix i).filter fun k => w k = false) =
      ((wordPrefix i).filter fun k => ¬ w k = true) := by
    ext k
    simp
  rw [hf, Finset.card_filter_add_card_filter_not]
  unfold wordPrefix
  simpa [Nat.min_eq_right (Nat.le_of_lt_succ i.isLt)] using Fin.card_filter_val_lt (n := n) (m := i.val)

theorem horizontalCount_le {n : ℕ} (w : Fin n → Bool) (i : Fin (n + 1)) :
    horizontalCount w i ≤ i := by
  rw [← horizontalCount_add_verticalCount w i]
  exact Nat.le_add_right _ _

theorem verticalCount_le {n : ℕ} (w : Fin n → Bool) (i : Fin (n + 1)) :
    verticalCount w i ≤ i := by
  rw [← horizontalCount_add_verticalCount w i]
  exact Nat.le_add_left _ _

/-- Horizontal-letter counts are monotone as the prefix endpoint increases. -/
theorem horizontalCount_mono {n : ℕ} (w : Fin n → Bool)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    horizontalCount w i ≤ horizontalCount w j := by
  unfold horizontalCount
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨wordPrefix_mono hij hk.1, hk.2⟩

/-- Vertical-letter counts are monotone as the prefix endpoint increases. -/
theorem verticalCount_mono {n : ℕ} (w : Fin n → Bool)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    verticalCount w i ≤ verticalCount w j := by
  unfold verticalCount
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨wordPrefix_mono hij hk.1, hk.2⟩

/-- A true letter contributes one new horizontal step. -/
theorem horizontalCount_succ_of_true {n : ℕ} (w : Fin n → Bool) (i : Fin n)
    (hi : w i = true) :
    horizontalCount w i.succ = horizontalCount w i.castSucc + 1 := by
  classical
  unfold horizontalCount
  rw [wordPrefix_succ, Finset.filter_insert]
  simp [hi, wordPrefix]

/-- A false letter contributes no new horizontal step. -/
theorem horizontalCount_succ_of_false {n : ℕ} (w : Fin n → Bool) (i : Fin n)
    (hi : w i = false) :
    horizontalCount w i.succ = horizontalCount w i.castSucc := by
  classical
  unfold horizontalCount
  rw [wordPrefix_succ, Finset.filter_insert]
  simp [hi]

/-- A true letter contributes no new vertical step. -/
theorem verticalCount_succ_of_true {n : ℕ} (w : Fin n → Bool) (i : Fin n)
    (hi : w i = true) :
    verticalCount w i.succ = verticalCount w i.castSucc := by
  classical
  unfold verticalCount
  rw [wordPrefix_succ, Finset.filter_insert]
  simp [hi]

/-- A false letter contributes one new vertical step. -/
theorem verticalCount_succ_of_false {n : ℕ} (w : Fin n → Bool) (i : Fin n)
    (hi : w i = false) :
    verticalCount w i.succ = verticalCount w i.castSucc + 1 := by
  classical
  unfold verticalCount
  rw [wordPrefix_succ, Finset.filter_insert]
  simp [hi, wordPrefix]

end ConstructionTargets.ProductSimplexWordPrefixCounts
