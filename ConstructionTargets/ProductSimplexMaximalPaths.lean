import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexMaximalPaths

universe u

open SSet

/-- Maximal nondegenerate simplices in the simplicial product of two standard simplices. -/
abbrev MaximalPath (p q : ℕ) :=
  (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)

/-- A maximal product simplex is exactly a monotone lattice path whose coordinate sum is time. -/
theorem mem_maximalPath_iff {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋p + q⦌) :
    z ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate (p + q) ↔
      SSet.prodStdSimplex.orderHomOfSimplex z rfl = .id :=
  SSet.prodStdSimplex.nonDegenerate_max_dim_iff z rfl

/-- The lattice path attached to a maximal product simplex advances through every time index. -/
theorem maximalPath_coordinate_sum {p q : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (i : Fin (p + q + 1)) :
    ((SSet.prodStdSimplex.objEquiv z.1 i).1 : ℕ) +
        (SSet.prodStdSimplex.objEquiv z.1 i).2 = i := by
  have h := (SSet.prodStdSimplex.nonDegenerate_max_dim_iff z.1 rfl).mp z.2
  have hi := DFunLike.congr_fun h i
  simpa [SSet.prodStdSimplex.orderHomOfSimplex] using congrArg Fin.val hi

/-- Simplicial faces delete the indicated lattice-path vertex. -/
theorem face_objEquiv {p q n : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n + 1⦌)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    SSet.prodStdSimplex.objEquiv ((Δ[p] ⊗ Δ[q]).δ i z) j =
      SSet.prodStdSimplex.objEquiv z (i.succAbove j) :=
  SSet.prodStdSimplex.objEquiv_δ_apply z i j


end ConstructionTargets.ProductSimplexMaximalPaths
