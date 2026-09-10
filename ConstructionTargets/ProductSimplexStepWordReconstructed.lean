import ConstructionTargets.ProductSimplexReconstructedPath
import ConstructionTargets.ProductSimplexStepWord
import ConstructionTargets.ProductSimplexWordPrefixCounts

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexStepWordReconstructed

universe u
open SSet
open ConstructionTargets.ProductSimplexBalancedWords
open ConstructionTargets.ProductSimplexCumulativeOrderHom
open ConstructionTargets.ProductSimplexMaximalPaths
open ConstructionTargets.ProductSimplexReconstructedPath
open ConstructionTargets.ProductSimplexStepWord
open ConstructionTargets.ProductSimplexUnitSteps
open ConstructionTargets.ProductSimplexWordPrefixCounts

/-- Reading the steps of the cumulative-count reconstruction recovers every input letter. -/
theorem stepWord_reconstructedPath {p q : ℕ} (w : BalancedWord p q) :
    stepWord (reconstructedPath w) = w.toWord := by
  funext i
  cases hi : w.toWord i with
  | false =>
      apply (stepWord_eq_false_iff _ i).mpr
      intro hh
      have hs := (isHorizontal_iff_first_coordinate_succ _ i).mp hh
      have hc := horizontalCount_succ_of_false w.toWord i hi
      change
        ((cumulativeOrderHom w i.succ).1 : ℕ) =
          (cumulativeOrderHom w i.castSucc).1 + 1 at hs
      simp only [cumulativeOrderHom_fst] at hs
      omega
  | true =>
      apply (stepWord_eq_true_iff _ i).mpr
      apply (isHorizontal_iff_first_coordinate_succ _ i).mpr
      change
        ((cumulativeOrderHom w i.succ).1 : ℕ) =
          (cumulativeOrderHom w i.castSucc).1 + 1
      simpa only [cumulativeOrderHom_fst] using
        horizontalCount_succ_of_true w.toWord i hi

#print axioms stepWord_reconstructedPath

end ConstructionTargets.ProductSimplexStepWordReconstructed
