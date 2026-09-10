import ConstructionTargets.ProductSimplexBalancedWords
import ConstructionTargets.ProductSimplexPathEndpoints
import ConstructionTargets.ProductSimplexStepWord
import ConstructionTargets.ProductSimplexWordPrefixCounts

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexPathWordBalance

universe u
open SSet
open ConstructionTargets.ProductSimplexBalancedWords
open ConstructionTargets.ProductSimplexMaximalPaths
open ConstructionTargets.ProductSimplexPathEndpoints
open ConstructionTargets.ProductSimplexStepWord
open ConstructionTargets.ProductSimplexWordPrefixCounts

/-- Horizontal prefix counts of a path's step word recover its first coordinate. -/
theorem horizontalCount_stepWord {p q : ℕ} (z : MaximalPath p q)
    (i : Fin (p + q + 1)) :
    horizontalCount (stepWord z) i = ((SSet.prodStdSimplex.objEquiv z.1 i).1 : ℕ) := by
  induction i using Fin.induction with
  | zero =>
      have hc := horizontalCount_add_verticalCount (stepWord z) (0 : Fin (p + q + 1))
      simp only [Fin.val_zero] at hc
      have hz : horizontalCount (stepWord z) (0 : Fin (p + q + 1)) = 0 := by omega
      rw [hz]
      have h := congrArg Prod.fst (grid_start z)
      exact congrArg Fin.val h.symm
  | succ j ih =>
      cases hj : stepWord z j with
      | false =>
          rw [horizontalCount_succ_of_false _ j hj, ih]
          exact (stepWord_false_coordinates z j hj).1.symm
      | true =>
          rw [horizontalCount_succ_of_true _ j hj, ih]
          exact (stepWord_true_coordinates z j hj).1.symm

/-- Vertical prefix counts of a path's step word recover its second coordinate. -/
theorem verticalCount_stepWord {p q : ℕ} (z : MaximalPath p q)
    (i : Fin (p + q + 1)) :
    verticalCount (stepWord z) i = ((SSet.prodStdSimplex.objEquiv z.1 i).2 : ℕ) := by
  have hp := horizontalCount_add_verticalCount (stepWord z) i
  have hh := horizontalCount_stepWord z i
  have hz := maximalPath_coordinate_sum z i
  omega

noncomputable section

/-- The step word extracted from a maximal path has the prescribed totals. -/
def balancedStepWord {p q : ℕ} (z : MaximalPath p q) : BalancedWord p q where
  toWord := stepWord z
  horizontal_total := by
    rw [horizontalCount_stepWord]
    have h := congrArg Prod.fst (grid_end z)
    exact congrArg Fin.val h
  vertical_total := by
    rw [verticalCount_stepWord]
    have h := congrArg Prod.snd (grid_end z)
    exact congrArg Fin.val h

@[simp] theorem balancedStepWord_toWord {p q : ℕ} (z : MaximalPath p q) :
    (balancedStepWord z).toWord = stepWord z := rfl

#print axioms horizontalCount_stepWord
#print axioms verticalCount_stepWord
#print axioms balancedStepWord

end

end ConstructionTargets.ProductSimplexPathWordBalance
