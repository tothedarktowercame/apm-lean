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

end ConstructionTargets.ProductSimplexBalancedWords
