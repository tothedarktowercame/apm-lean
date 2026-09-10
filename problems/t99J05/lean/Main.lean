import Mathlib
import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.RationalLefschetz

/-! # t99J05: complex projective fixed points, indices and Euler characteristic

The theorem states the generalized diagonal construction for every n. Its n=2
specialization is exactly [z0,z1,z2] ↦ [z0,2z1,3z2], covering every printed part.
Affine charts on the fixed quotient topology are an explicit construction
obligation. Local indices are real determinant signs of the actual local
coordinate map, with differentiability and nondegeneracy required. Global
Lefschetz and Euler numbers are computed from actual rational singular homology.
No fixed-point or Euler-characteristic formula is assumed as an input.
-/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.RationalLefschetz
noncomputable section

def T99J05Diagonal (n : ℕ) (v : Vectors ℂ n) : Vectors ℂ n :=
  fun i => ((i.val + 1 : ℕ) : ℂ) * v i

theorem apm_t99j05 :
    ∀ n : ℕ, AffineChartConstruction n ∧
      ∃ f : ContinuousMap (CP n) (CP n),
        (∀ v : NonzeroVectors ℂ n, ∃ hv : T99J05Diagonal n v.val ≠ 0,
          f (quotientMap ℂ n v) = quotientMap ℂ n ⟨T99J05Diagonal n v.val,hv⟩) ∧
        ContinuousMap.Homotopic f (ContinuousMap.id (CP n)) ∧
        (∀ p : CP n, f p = p ↔ ∃ i : Fin (n + 1), p = coordinateLine ℂ n i) ∧
        (∀ i : Fin (n + 1), ContDiffAt ℝ 1 (localMap f i) 0 ∧
          fixedPointDeterminant f i ≠ 0 ∧ localIndex f i = 1) ∧
        HasLefschetzNumber f (∑ i : Fin (n + 1), (localIndex f i : ℚ)) ∧
        HasEulerCharacteristic (CP n) (∑ i : Fin (n + 1), (localIndex f i : ℚ)) ∧
        HasEulerCharacteristic (CP n) ((n : ℚ) + 1) := by
  sorry
