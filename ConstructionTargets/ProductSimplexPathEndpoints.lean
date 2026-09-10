import ConstructionTargets.ProductSimplexStepWord

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexPathEndpoints

universe u
open SSet
open ConstructionTargets.ProductSimplexMaximalPaths

/-- A maximal product-simplex path begins at the lower-left grid vertex. -/
theorem grid_start {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    SSet.prodStdSimplex.objEquiv z.1 0 = ((0 : Fin (p + 1)), (0 : Fin (q + 1))) := by
  have h := maximalPath_coordinate_sum z (0 : Fin (p + q + 1))
  apply Prod.ext
  · apply Fin.ext
    change ((SSet.prodStdSimplex.objEquiv z.1 0).1 : ℕ) = 0
    have hn : ((SSet.prodStdSimplex.objEquiv z.1 0).1 : ℕ) +
        (SSet.prodStdSimplex.objEquiv z.1 0).2 = 0 := by simpa using h
    omega
  · apply Fin.ext
    change ((SSet.prodStdSimplex.objEquiv z.1 0).2 : ℕ) = 0
    have hn : ((SSet.prodStdSimplex.objEquiv z.1 0).1 : ℕ) +
        (SSet.prodStdSimplex.objEquiv z.1 0).2 = 0 := by simpa using h
    omega

/-- A maximal product-simplex path ends at the upper-right grid vertex. -/
theorem grid_end {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    SSet.prodStdSimplex.objEquiv z.1 (Fin.last (p + q)) =
      (Fin.last p, Fin.last q) := by
  have h := maximalPath_coordinate_sum z (Fin.last (p + q))
  have hn : ((SSet.prodStdSimplex.objEquiv z.1 (Fin.last (p + q))).1 : ℕ) +
      (SSet.prodStdSimplex.objEquiv z.1 (Fin.last (p + q))).2 = p + q := by
    simpa using h
  have hfst := (SSet.prodStdSimplex.objEquiv z.1 (Fin.last (p + q))).1.isLt
  have hsnd := (SSet.prodStdSimplex.objEquiv z.1 (Fin.last (p + q))).2.isLt
  apply Prod.ext
  · apply Fin.ext
    change ((SSet.prodStdSimplex.objEquiv z.1 (Fin.last (p + q))).1 : ℕ) = p
    omega
  · apply Fin.ext
    change ((SSet.prodStdSimplex.objEquiv z.1 (Fin.last (p + q))).2 : ℕ) = q
    omega


end ConstructionTargets.ProductSimplexPathEndpoints
