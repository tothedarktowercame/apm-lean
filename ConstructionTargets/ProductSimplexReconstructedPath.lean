import ConstructionTargets.ProductSimplexCumulativeOrderHom
import ConstructionTargets.ProductSimplexMaximalPaths

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexReconstructedPath

universe u
open SSet
open ConstructionTargets.ProductSimplexBalancedWords
open ConstructionTargets.ProductSimplexCumulativeOrderHom
open ConstructionTargets.ProductSimplexMaximalPaths

/-- The product simplex whose grid vertices are the cumulative word counts. -/
def reconstructedSimplex {p q : ℕ} (w : BalancedWord p q) :
    (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋p + q⦌ :=
  SSet.prodStdSimplex.objEquiv.symm (cumulativeOrderHom w)

@[simp] theorem reconstructedSimplex_objEquiv {p q : ℕ} (w : BalancedWord p q) :
    SSet.prodStdSimplex.objEquiv (reconstructedSimplex w) = cumulativeOrderHom w := by
  exact SSet.prodStdSimplex.objEquiv.apply_symm_apply _

/-- The reconstructed simplex is maximal and nondegenerate. -/
def reconstructedPath {p q : ℕ} (w : BalancedWord p q) :
    (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q) := by
  let x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋p + q⦌ := reconstructedSimplex w
  refine ⟨x, ?_⟩
  rw [mem_maximalPath_iff]
  ext i
  change ((SSet.prodStdSimplex.objEquiv x i).1 : ℕ) +
      (SSet.prodStdSimplex.objEquiv x i).2 = i
  have hx : SSet.prodStdSimplex.objEquiv x = cumulativeOrderHom w := by
    dsimp [x, reconstructedSimplex]
    exact SSet.prodStdSimplex.objEquiv.apply_symm_apply _
  rw [hx]
  exact cumulativeOrderHom_coordinate_sum w i

end ConstructionTargets.ProductSimplexReconstructedPath
