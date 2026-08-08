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
  /-
  PARTIAL boundary (closer hop 1).

  A broader search found the useful endpoint API omitted by the imported
  notes: Mathlib's
  `AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
  kills every positive-degree homology object of a totally disconnected
  space, and
  `singularHomologyFunctorZeroOfTotallyDisconnectedSpace` identifies its
  zeroth homology with the coproduct of one coefficient object per point.
  Consequently the entire `n = 0` branch reduces concretely to proving that
  the metric sphere in `EuclideanSpace ℝ (Fin 1)` is the discrete two-point
  space and identifying the resulting two-object coproduct in `ModuleCat ℤ`
  with `ModuleCat.of ℤ (ℤ × ℤ)`.

  This does not address the positive-dimensional branch. Searches of
  `LEMMA-INDEX.md`, all `ConstructionTargets/`, the sphere/homology siblings
  (`t02A06`, `t02A08`, `t94J08`, `t95J04`, `t96A03`), Mathlib's singular-set,
  singular-chain, homology, suspension, CW-complex, and reduced-homology
  sources, and git history found no suspension isomorphism, cellular-to-
  singular comparison, Mayer--Vietoris sequence, or compiled homology
  computation for metric spheres. Functoriality alone cannot produce either
  the top-dimensional generator or the off-degree vanishing. Thus even after
  the zero-sphere reduction, the frozen universal positive-dimensional claim
  still requires substantial missing algebraic-topology infrastructure. The
  statement is unchanged.
  -/
  sorry
