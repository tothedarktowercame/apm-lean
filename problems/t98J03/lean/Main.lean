import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t98J03 — integral homology of spheres

## Statement repairs

None.

## Encoding questions

None. `Sⁿ` is the actual unit metric sphere in `ℝⁿ⁺¹`, and homology is
Mathlib's integral singular homology. The disconnected zero-sphere is stated
separately from the positive-dimensional formula.
-/

open CategoryTheory

noncomputable section

abbrev apm_t98J03_Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev apm_t98J03_H (n k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (apm_t98J03_Sphere n)))

theorem apm_t98j03 :
    Nonempty (apm_t98J03_H 0 0 ≅ ModuleCat.of ℤ (ℤ × ℤ)) ∧
    (∀ k : ℕ, 0 < k → Limits.IsZero (apm_t98J03_H 0 k)) ∧
    ∀ n : ℕ, 0 < n →
      Nonempty (apm_t98J03_H n 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t98J03_H n n ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k : ℕ, k ≠ 0 → k ≠ n → Limits.IsZero (apm_t98J03_H n k) := by
  sorry
