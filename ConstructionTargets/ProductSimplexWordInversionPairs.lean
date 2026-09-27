import ConstructionTargets.ProductSimplexInversionCardParity

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexWordInversionPairs

universe u
open SSet
open ProductSimplexShuffleParity
open ProductSimplexMaximalPaths
open ProductSimplexWordPathEquivalence
open ProductSimplexPathWordBalance
open ProductSimplexStepWord

/-- Inversion pairs of a Boolean step word: a vertical letter before a
horizontal letter. -/
def wordInversionPairs {m : ℕ} (w : Fin m → Bool) :
    Finset (Fin m × Fin m) :=
  Finset.univ.filter fun ij => ij.1 < ij.2 ∧ w ij.1 = false ∧ w ij.2 = true

/-- The geometric inversion set of a maximal path is exactly the inversion
set of its reviewed balanced step word. -/
theorem inversionPairs_eq_wordInversionPairs {p q : ℕ}
    (z : MaximalPath.{u} p q) :
    inversionPairs z =
      wordInversionPairs ((wordPathEquiv.{u} p q).symm z).toWord := by
  classical
  ext ij
  simp only [inversionPairs, wordInversionPairs, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change (ij.1 < ij.2 ∧ ¬ IsHorizontal z ij.1 ∧ IsHorizontal z ij.2) ↔
    (ij.1 < ij.2 ∧ stepWord z ij.1 = false ∧ stepWord z ij.2 = true)
  simp

#print axioms wordInversionPairs
#print axioms inversionPairs_eq_wordInversionPairs

end ConstructionTargets.ProductSimplexWordInversionPairs
