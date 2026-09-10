import ConstructionTargets.ProductSimplexAffineRealization

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexUnitSteps

universe u
open SSet
open ConstructionTargets.ProductSimplexMaximalPaths

/-- Consecutive vertices of a maximal product-simplex path differ by one coordinate unit. -/
theorem horizontal_or_vertical_unit_step {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (i : Fin (p + q)) :
    (((SSet.prodStdSimplex.objEquiv z.1 i.succ).1 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 + 1 ∧
      ((SSet.prodStdSimplex.objEquiv z.1 i.succ).2 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).2) ∨
    (((SSet.prodStdSimplex.objEquiv z.1 i.succ).1 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 ∧
      ((SSet.prodStdSimplex.objEquiv z.1 i.succ).2 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).2 + 1) := by
  have hm := (SSet.prodStdSimplex.objEquiv z.1).monotone i.castSucc_le_succ
  have h0 := maximalPath_coordinate_sum z i.castSucc
  have h1 := maximalPath_coordinate_sum z i.succ
  have h0' : ((SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 : ℕ) +
      (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).2 = i.val := by simpa using h0
  have h1' : ((SSet.prodStdSimplex.objEquiv z.1 i.succ).1 : ℕ) +
      (SSet.prodStdSimplex.objEquiv z.1 i.succ).2 = i.val + 1 := by simpa using h1
  have hm1 := hm.1
  have hm2 := hm.2
  omega

/-- Horizontal steps are exactly those in the first disjunct. -/
theorem isHorizontal_iff_first_coordinate_succ {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (i : Fin (p + q)) :
    ConstructionTargets.ProductSimplexShuffleParity.IsHorizontal z i ↔
      ((SSet.prodStdSimplex.objEquiv z.1 i.succ).1 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 + 1 := by
  rcases horizontal_or_vertical_unit_step z i with h | h
  · change ((SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 : ℕ) <
      (SSet.prodStdSimplex.objEquiv z.1 i.succ).1 ↔ _
    omega
  · change ((SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 : ℕ) <
      (SSet.prodStdSimplex.objEquiv z.1 i.succ).1 ↔ _
    omega


end ConstructionTargets.ProductSimplexUnitSteps
