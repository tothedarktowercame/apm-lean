import ConstructionTargets.ProductSimplexPathEndpoints

namespace ConstructionTargets.ProductSimplexWordPrefixCounts

private def wordPrefix {n : ℕ} (i : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun k => k.val < i.val

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

end ConstructionTargets.ProductSimplexWordPrefixCounts
