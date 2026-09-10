import ConstructionTargets.ProductSimplexMaximalPaths
import Mathlib.Data.ZMod.Basic

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexShuffleParity

universe u
open SSet
open ConstructionTargets.ProductSimplexMaximalPaths

/-- A step is horizontal when the first path coordinate strictly increases. -/
def IsHorizontal {p q : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) (i : Fin (p + q)) : Prop :=
  (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 <
    (SSet.prodStdSimplex.objEquiv z.1 i.succ).1

/-- Inversions are vertical steps occurring before horizontal steps. -/
noncomputable def inversionPairs {p q : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    Finset (Fin (p + q) × Fin (p + q)) := by
  classical
  exact Finset.univ.filter fun ij => ij.1 < ij.2 ∧ ¬ IsHorizontal z ij.1 ∧ IsHorizontal z ij.2

/-- The integer orientation sign of a maximal lattice path. -/
noncomputable def shuffleSign {p q : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) : ℤ :=
  (-1 : ℤ) ^ (inversionPairs z).card

@[simp] theorem shuffleSign_mul_self {p q : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    shuffleSign z * shuffleSign z = 1 := by
  simp [shuffleSign, ← mul_pow]

@[simp] theorem shuffleSign_ne_zero {p q : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    shuffleSign z ≠ 0 := by
  intro h
  have hs := shuffleSign_mul_self z
  rw [h] at hs
  norm_num at hs

@[simp] theorem shuffleSign_mod_two {p q : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    (shuffleSign z : ZMod 2) = 1 := by
  simp [shuffleSign]


end ConstructionTargets.ProductSimplexShuffleParity
