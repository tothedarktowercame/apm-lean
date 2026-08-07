import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t96A03 — two 2-spheres glued along their equators

## Statement repairs

The review packet suggests `H₂(X) = ℤ²`, but this is not the homology of the
space in the source. Mayer–Vietoris gives
`0 → ℤ² → H₂(X) → ℤ → 0`, so `H₂(X) ≅ ℤ³`. Equivalently, the quotient has
four 2-cells attached to one circle, with a rank-one cellular boundary map.
The statement below records the corrected value `ℤ³`.

## Encoding questions

None. Both spheres, their equator, the gluing homeomorphism, the quotient
space, and Mathlib's integral singular homology functor are used directly.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t96A03_Sphere2 :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def apm_t96A03_Equator : Set apm_t96A03_Sphere2 :=
  {x | (x.1 : EuclideanSpace ℝ (Fin 3)) 2 = 0}

abbrev apm_t96A03_EquatorSpace := apm_t96A03_Equator

inductive apm_t96A03_glueRel
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2 →
      Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2 → Prop
  | glue (x : apm_t96A03_EquatorSpace) :
      apm_t96A03_glueRel h (Sum.inl x.1) (Sum.inr (h x).1)

def apm_t96A03_X
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :=
  Quotient (Relation.EqvGen.setoid (apm_t96A03_glueRel h))

noncomputable instance
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    TopologicalSpace (apm_t96A03_X h) :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2 ↦ Quotient.mk _ x)
    inferInstance

abbrev apm_t96A03_H (k : ℕ) (Y : Type) [TopologicalSpace Y] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))

theorem apm_t96a03
    (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) :
    Nonempty (apm_t96A03_H 0 (apm_t96A03_X h) ≅ ModuleCat.of ℤ ℤ) ∧
    Limits.IsZero (apm_t96A03_H 1 (apm_t96A03_X h)) ∧
    Nonempty
      (apm_t96A03_H 2 (apm_t96A03_X h) ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t96A03_H k (apm_t96A03_X h)) := by
  sorry
