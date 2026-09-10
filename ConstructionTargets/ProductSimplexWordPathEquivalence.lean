import ConstructionTargets.ProductSimplexPathWordBalance
import ConstructionTargets.ProductSimplexReconstructedPath
import ConstructionTargets.ProductSimplexStepWordReconstructed

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexWordPathEquivalence

open SSet
open ConstructionTargets.ProductSimplexBalancedWords
open ConstructionTargets.ProductSimplexCumulativeOrderHom
open ConstructionTargets.ProductSimplexMaximalPaths
open ConstructionTargets.ProductSimplexPathWordBalance
open ConstructionTargets.ProductSimplexReconstructedPath
open ConstructionTargets.ProductSimplexStepWordReconstructed

/-- Reconstructing the balanced step word extracted from a maximal path returns that path. -/
theorem reconstructedPath_balancedStepWord {p q : ℕ} (z : MaximalPath p q) :
    reconstructedPath (balancedStepWord z) = z := by
  apply Subtype.ext
  change reconstructedSimplex (balancedStepWord z) = z.1
  apply SSet.prodStdSimplex.objEquiv.injective
  rw [reconstructedSimplex_objEquiv]
  ext i
  · exact horizontalCount_stepWord z i
  · exact verticalCount_stepWord z i

noncomputable section

/-- Balanced Boolean words and canonical maximal product-simplex paths are exactly equivalent. -/
noncomputable def wordPathEquiv (p q : ℕ) : BalancedWord p q ≃ MaximalPath p q where
  toFun := reconstructedPath
  invFun := balancedStepWord
  left_inv w := by
    cases w
    simp only [balancedStepWord]
    congr
    exact stepWord_reconstructedPath _
  right_inv := reconstructedPath_balancedStepWord

example : BalancedWord 0 0 ≃ MaximalPath 0 0 := wordPathEquiv 0 0
example : BalancedWord 0 1 ≃ MaximalPath 0 1 := wordPathEquiv 0 1
example : BalancedWord 1 0 ≃ MaximalPath 1 0 := wordPathEquiv 1 0
example : BalancedWord 0 2 ≃ MaximalPath 0 2 := wordPathEquiv 0 2
example : BalancedWord 1 1 ≃ MaximalPath 1 1 := wordPathEquiv 1 1
example : BalancedWord 2 0 ≃ MaximalPath 2 0 := wordPathEquiv 2 0
example : BalancedWord 0 3 ≃ MaximalPath 0 3 := wordPathEquiv 0 3
example : BalancedWord 1 2 ≃ MaximalPath 1 2 := wordPathEquiv 1 2
example : BalancedWord 2 1 ≃ MaximalPath 2 1 := wordPathEquiv 2 1
example : BalancedWord 3 0 ≃ MaximalPath 3 0 := wordPathEquiv 3 0
example : BalancedWord 0 4 ≃ MaximalPath 0 4 := wordPathEquiv 0 4
example : BalancedWord 1 3 ≃ MaximalPath 1 3 := wordPathEquiv 1 3
example : BalancedWord 2 2 ≃ MaximalPath 2 2 := wordPathEquiv 2 2
example : BalancedWord 3 1 ≃ MaximalPath 3 1 := wordPathEquiv 3 1
example : BalancedWord 4 0 ≃ MaximalPath 4 0 := wordPathEquiv 4 0

#print axioms reconstructedPath_balancedStepWord
#print axioms wordPathEquiv

end

end ConstructionTargets.ProductSimplexWordPathEquivalence
