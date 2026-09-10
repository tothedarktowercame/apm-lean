import ConstructionTargets.ProductSimplexWordPrefixCounts

namespace ConstructionTargets.ProductSimplexBalancedWords

open ConstructionTargets.ProductSimplexWordPrefixCounts

/-- A Boolean word with the prescribed total numbers of horizontal and vertical letters. -/
structure BalancedWord (p q : ℕ) where
  toWord : Fin (p + q) → Bool
  horizontal_total : horizontalCount toWord (Fin.last (p + q)) = p
  vertical_total : verticalCount toWord (Fin.last (p + q)) = q

instance (p q : ℕ) : CoeFun (BalancedWord p q) (fun _ => Fin (p + q) → Bool) :=
  ⟨BalancedWord.toWord⟩

theorem terminal_partition {p q : ℕ} (w : BalancedWord p q) :
    horizontalCount w.toWord (Fin.last (p + q)) +
      verticalCount w.toWord (Fin.last (p + q)) = p + q := by
  rw [w.horizontal_total, w.vertical_total]

namespace BalancedWord

/-- Every horizontal prefix count is bounded by the prescribed horizontal total. -/
theorem horizontalCount_le_total {p q : ℕ} (w : BalancedWord p q)
    (i : Fin (p + q + 1)) : horizontalCount w.toWord i ≤ p := by
  calc
    horizontalCount w.toWord i ≤ horizontalCount w.toWord (Fin.last (p + q)) :=
      horizontalCount_mono w.toWord (Fin.le_last i)
    _ = p := w.horizontal_total

/-- Every vertical prefix count is bounded by the prescribed vertical total. -/
theorem verticalCount_le_total {p q : ℕ} (w : BalancedWord p q)
    (i : Fin (p + q + 1)) : verticalCount w.toWord i ≤ q := by
  calc
    verticalCount w.toWord i ≤ verticalCount w.toWord (Fin.last (p + q)) :=
      verticalCount_mono w.toWord (Fin.le_last i)
    _ = q := w.vertical_total

end BalancedWord

end ConstructionTargets.ProductSimplexBalancedWords
