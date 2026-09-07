import Mathlib

/-! # lts-ultraproduct-thm1: ultraproducts commute with factor algebras

## Statement repairs

The statement is encoded at the level of underlying sets with a family of
setoid congruences.  Operations and compatibility axioms are irrelevant to the
canonical bijection and are therefore not added.

## Encoding questions

Both sides are concrete quotient types.  `quotientAfter` first identifies
pointwise-congruent representatives modulo the ultrafilter; `quotientBefore`
first forms each factor and then takes their ultraproduct.
-/

namespace APMLTSUltraproduct

def moduloSetoid {I : Type*} (D : Ultrafilter I) (A : I → Type*)
    (σ : ∀ i, Setoid (A i)) : Setoid (∀ i, A i) where
  r f g := {i | (σ i).r (f i) (g i)} ∈ D
  iseqv := by
    constructor
    · intro f
      convert D.univ_mem using 1
      ext i
      simp
    · intro f g hfg
      filter_upwards [hfg] with i hi
      exact (σ i).symm hi
    · intro f g h hfg hgh
      filter_upwards [hfg, hgh] with i hi₁ hi₂
      exact (σ i).trans hi₁ hi₂

def equalitySetoid {I : Type*} (D : Ultrafilter I) (B : I → Type*) :
    Setoid (∀ i, B i) where
  r f g := {i | f i = g i} ∈ D
  iseqv := by
    constructor
    · intro f
      convert D.univ_mem using 1
      ext i
      simp
    · intro f g hfg
      filter_upwards [hfg] with i hi
      exact hi.symm
    · intro f g h hfg hgh
      filter_upwards [hfg, hgh] with i hi₁ hi₂
      exact hi₁.trans hi₂

def quotientAfter {I : Type*} (D : Ultrafilter I) (A : I → Type*)
    (σ : ∀ i, Setoid (A i)) := Quotient (moduloSetoid D A σ)

def quotientBefore {I : Type*} (D : Ultrafilter I) (A : I → Type*)
    (σ : ∀ i, Setoid (A i)) :=
  Quotient (equalitySetoid D (fun i => Quotient (σ i)))

end APMLTSUltraproduct

theorem apm_lts_ultraproduct_thm1
    {I : Type*} [Nonempty I] (D : Ultrafilter I)
    (A : I → Type*) (σ : ∀ i, Setoid (A i)) :
    Nonempty (APMLTSUltraproduct.quotientAfter D A σ ≃
      APMLTSUltraproduct.quotientBefore D A σ) := by
  sorry
