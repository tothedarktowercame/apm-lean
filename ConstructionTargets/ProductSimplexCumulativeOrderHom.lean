import ConstructionTargets.ProductSimplexBalancedWords

namespace ConstructionTargets.ProductSimplexCumulativeOrderHom

open ConstructionTargets.ProductSimplexWordPrefixCounts
open ConstructionTargets.ProductSimplexBalancedWords

/-- The bounded grid vertex determined by the two prefix counts. -/
def gridVertex {p q : ℕ} (w : BalancedWord p q) (i : Fin (p + q + 1)) :
    Fin (p + 1) × Fin (q + 1) :=
  (⟨horizontalCount w.toWord i, Nat.lt_succ_of_le (w.horizontalCount_le_total i)⟩,
   ⟨verticalCount w.toWord i, Nat.lt_succ_of_le (w.verticalCount_le_total i)⟩)

/-- Cumulative prefix counts form the required monotone grid path. -/
def cumulativeOrderHom {p q : ℕ} (w : BalancedWord p q) :
    Fin (p + q + 1) →o Fin (p + 1) × Fin (q + 1) where
  toFun := gridVertex w
  monotone' _i _j hij :=
    ⟨horizontalCount_mono w.toWord hij, verticalCount_mono w.toWord hij⟩

@[simp] theorem cumulativeOrderHom_fst {p q : ℕ} (w : BalancedWord p q)
    (i : Fin (p + q + 1)) :
    ((cumulativeOrderHom w i).1 : ℕ) = horizontalCount w.toWord i := rfl

@[simp] theorem cumulativeOrderHom_snd {p q : ℕ} (w : BalancedWord p q)
    (i : Fin (p + q + 1)) :
    ((cumulativeOrderHom w i).2 : ℕ) = verticalCount w.toWord i := rfl

theorem cumulativeOrderHom_coordinate_sum {p q : ℕ} (w : BalancedWord p q)
    (i : Fin (p + q + 1)) :
    ((cumulativeOrderHom w i).1 : ℕ) + (cumulativeOrderHom w i).2 = i := by
  exact horizontalCount_add_verticalCount w.toWord i

end ConstructionTargets.ProductSimplexCumulativeOrderHom
#print axioms ConstructionTargets.ProductSimplexCumulativeOrderHom.cumulativeOrderHom_fst
#print axioms ConstructionTargets.ProductSimplexCumulativeOrderHom.cumulativeOrderHom_snd
#print axioms ConstructionTargets.ProductSimplexCumulativeOrderHom.cumulativeOrderHom_coordinate_sum
