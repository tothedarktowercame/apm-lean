import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup

/-!
# APM t97J04

## Statement repairs

The spelling `meridinal` is corrected to `meridional`. No mathematical
hypothesis or conclusion is changed.

## Encoding questions

The given decomposition deformation retracts to a torus wedged with the
remaining longitude circle. Following `t02A03`, this is retained as an actual
topological quotient rather than a numerical surrogate. Its fundamental group
is the actual presented group `<a,b,d | [a,b]>`, and its homology groups are
integral singular homology objects in `ModuleCat ℤ`.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t97J04_Torus := Circle × Circle

/-- Glue the remaining longitude circle to the torus at their basepoints. -/
inductive apm_t97J04_WedgeRel :
    Sum apm_t97J04_Torus Circle → Sum apm_t97J04_Torus Circle → Prop
  | base : apm_t97J04_WedgeRel (.inl (1, 1)) (.inr 1)

/-- The concrete deformation-retract model `T² ∨ S¹` of the specified finite
complex. -/
def apm_t97J04_X :=
  Quotient (Relation.EqvGen.setoid apm_t97J04_WedgeRel)

noncomputable instance : TopologicalSpace apm_t97J04_X :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97J04_Torus Circle ↦ Quotient.mk _ x) inferInstance

def apm_t97J04_basepoint : apm_t97J04_X :=
  Quotient.mk _ (.inl (1, 1))

/-- The two chosen basepoints are identified in the concrete wedge quotient. -/
lemma apm_t97J04_inl_base_eq_inr_base :
    (Quotient.mk _ (.inl (1, 1)) : apm_t97J04_X) =
      Quotient.mk _ (.inr 1) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ apm_t97J04_WedgeRel.base

/-- The relation `[a,b]` in the requested three-generator presentation. -/
def apm_t97J04_relator : FreeGroup (Fin 3) :=
  FreeGroup.of 0 * FreeGroup.of 1 *
    (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

abbrev apm_t97J04_piOne :=
  PresentedGroup ({apm_t97J04_relator} : Set (FreeGroup (Fin 3)))

/-- Integral singular homology of the specified complex. -/
abbrev apm_t97J04_H (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t97J04_X))

theorem apm_t97j04 :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        apm_t97J04_piOne) ∧
    Nonempty (apm_t97J04_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97J04_H 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97J04_H 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t97J04_H k) := by
  /-
  PARTIAL boundary (closer hop 1).

  The concrete quotient bookkeeping now has a compiled basepoint bridge:
  `apm_t97J04_inl_base_eq_inr_base` proves that the torus and circle
  basepoints agree in `apm_t97J04_X` directly from the generating relation.

  The remaining proof needs Seifert--van Kampen for this EqvGen quotient to
  identify its fundamental group with the frozen presentation, and singular
  Mayer--Vietoris (or a cellular-to-singular comparison) to compute all four
  homology claims.  `t02A03` uses the identical `T² ∨ S¹` quotient and records
  the same boundary.  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
  closed topology artifacts, Mathlib's fundamental-groupoid product/pushout
  sources, singular homology, exact-sequence and CW-complex sources, and git
  history found product preservation but no circle fundamental-group
  computation, van Kampen theorem, singular Mayer--Vietoris sequence, or
  cellular comparison theorem capable of closing these frozen conjuncts.
  -/
  sorry
