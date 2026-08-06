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

Mathlib has no construction for the specified finite complex obtained by
gluing the two punctured tori after attaching the meridian disk. That exact
adjunction space is therefore isolated as a typed opaque object; it is not
replaced by a homotopy-equivalent numerical surrogate. Its fundamental group
is stated as the actual presented group
`<a,b,d | [a,b]>`, and its homology groups are actual integral singular
homology objects in `ModuleCat ℤ`.
-/

open CategoryTheory Set

noncomputable section

/-- The finite complex obtained by gluing the punctured torus `T` to the
punctured torus with a meridian disk attached, along their common boundary. -/
opaque apm_t97J04_X : Type

axiom apm_t97J04_X_nonempty : Nonempty apm_t97J04_X

opaque apm_t97J04_X_topology : TopologicalSpace apm_t97J04_X

noncomputable instance : TopologicalSpace apm_t97J04_X :=
  apm_t97J04_X_topology

def apm_t97J04_basepoint : apm_t97J04_X :=
  Classical.choice apm_t97J04_X_nonempty

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
  sorry
