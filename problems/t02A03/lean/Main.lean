import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

open CategoryTheory

/-!
# APM t02A03 — complements of core circles in handlebodies

## Statement repairs

None.

## Encoding note

The two complements are represented by their explicit deformation-retract
models: a torus, and the wedge of a torus with a circle.  Unlike a list of
Betti numbers, the second model remains an actual topological quotient, so its
fundamental group and singular homology are the subjects of the statement.
-/

abbrev apm_t02a03_Torus := Circle × Circle

inductive apm_t02a03_WedgeGlue :
    Sum apm_t02a03_Torus Circle → Sum apm_t02a03_Torus Circle → Prop
  | base : apm_t02a03_WedgeGlue (.inl (1, 1)) (.inr 1)

def apm_t02a03_Y :=
  Quotient (Relation.EqvGen.setoid apm_t02a03_WedgeGlue)

noncomputable instance : TopologicalSpace apm_t02a03_Y :=
  TopologicalSpace.coinduced
    (fun a => Quotient.mk (Relation.EqvGen.setoid apm_t02a03_WedgeGlue) a)
    inferInstance

noncomputable def apm_t02a03_ybase : apm_t02a03_Y :=
  Quotient.mk _ (.inl (1, 1))

theorem apm_t02a03 :
    Nonempty
      (FundamentalGroup apm_t02a03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) ∧
    Nonempty
      (FundamentalGroup apm_t02a03_Y apm_t02a03_ybase ≃*
        Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅
        ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y) ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ n : ℕ, 3 ≤ n →
      Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a03_Y))) := by
  sorry
